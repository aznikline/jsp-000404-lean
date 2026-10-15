import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S4
import Jsp000404.R1LeavesN7_17S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h2153 | h2153
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6_x1_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h2153
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6_x1_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h2153

set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7

set_option maxHeartbeats 7146000 in
set_option maxHeartbeats 7146000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s5 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3501 | h3501
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3502 | h3502
      · linarith only [h3502, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3504 | h3504
        · linarith only [h3501, h3504, h4, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3506 | h3506
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3507 | h3507
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3508 | h3508
              · linarith only [h0, h3501, h3508, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3510 | h3510
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3511 | h3511
                  · linarith only [h2, h3504, h3511, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3513 | h3513
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3514 | h3514
                      · linarith only [h0, h2, h3501, h3502, h3506, h3514, h6, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3516 | h3516
                        · linarith only [h2, h3504, h3507, h3513, h3516, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h3506, h3513, h3516, h6, hc34, hc45, hlam, hphi]
                    · linarith only [h3501, h3502, h3513, hc23, hc35, hlam, hphi]
                · linarith only [h3501, h3502, h3510, hc13, hc35, hlam, hphi]
            · linarith only [h3507, h5, h6, hc12, hc25, hlam, hphi]
          · linarith only [h3506, h4, h6, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3523 | h3523
      · linarith only [h3523, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3525 | h3525
        · linarith only [h3525, h5, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3527 | h3527
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3528 | h3528
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3529 | h3529
              · linarith only [h0, h3529, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3531 | h3531
                · linarith only [h1, h3501, h3531, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3533 | h3533
                  · linarith only [h2, h3525, h3533, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3535 | h3535
                    · linarith only [h1, h3501, h3535, h4, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3537 | h3537
                      · linarith only [h3523, h3537, h4, h6, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3539 | h3539
                        · linarith only [h0, h1, h3501, h3525, h3528, h3539, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3541 | h3541
                          · linarith only [h3539, h3541, h4, h6, hc23, hc34, hlam, hphi]
                          · rcases h0bigk with h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, h3528, h3535, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              rcases p3543_3 (m.d 0 1) (by simp) with h3546 | h3546
                              · rcases p3543_3 (m.d 0 2) (by simp) with h3547 | h3547
                                · linarith only [h0, h3547, hlam]
                                · linarith only [h3547, h4, hlam]
                              · linarith only [h1, h3546, hlam]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              rcases p3543_3 (m.d 0 1) (by simp) with h3551 | h3551
                              · rcases p3543_3 (m.d 0 2) (by simp) with h3552 | h3552
                                · linarith only [h0, h3552, hlam]
                                · linarith only [h3552, h5, hlam]
                              · linarith only [h2, h3551, hlam]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, h3528, h3535, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h1, h3527, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h1, h3501, h3527, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h6, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h1, hlam, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h4, hlam, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3501, hlam, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3523, hlam, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h2, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h5, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h1, h3527, h5, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3525, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, h3528, h3535, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h1, h3523, h3527, h3541, hc23, hc45, hlam, hphi, ht34, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3523, h3541, hc04, hc45, hlam, hphi, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [hlam, p3543_0]
            · linarith only [h3528, h5, h6, hc12, hc25, hlam, hphi]
          · linarith only [h3527, h4, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 7512000 in
set_option maxHeartbeats 7512000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s4 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_12_14_H_I_L_I_L_I_s5 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3579 | h3579
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3580 | h3580
      · linarith only [h3580, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3582 | h3582
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3583 | h3583
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3584 | h3584
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3585 | h3585
              · linarith only [h0, h3585, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3587 | h3587
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3588 | h3588
                  · linarith only [h1, h3580, h3588, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3590 | h3590
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3591 | h3591
                      · linarith only [h0, h3580, h3584, h3591, h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3593 | h3593
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3594 | h3594
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3595 | h3595
                            · rcases h0bigk with h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c | h3596c
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [hlam, p3596_0]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3593, h3595, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h1, h3584, h3593, h3595, hc01, hc45, hlam, hphi, ht0b, ht5b, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3593, h3595, h4, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                rcases p3596_3 (m.d 0 1) (by simp) with h3601 | h3601
                                · rcases p3596_3 (m.d 0 2) (by simp) with h3602 | h3602
                                  · linarith only [h0, h3602, hlam]
                                  · linarith only [h3579, h3602, hlam]
                                · linarith only [h3, h3601, hlam]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h0, hlam, p3596_0]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [hlam, p3596_0]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h1, h3584, h3593, h3595, hc02, hc45, hlam, hphi, ht0b, ht5b, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h5, hlam, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3591, h5, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h1, hlam, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h4, hlam, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [hlam, p3596_0]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3580, hlam, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3, h3587, h3591, h4, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h2, hlam, p3596_0]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3591, h5, hc02, hc34, hlam, hphi, ht23, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3591, h5, hc03, hc34, hlam, hphi, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [hlam, p3596_0]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                rcases p3596_3 (m.d 0 1) (by simp) with h3620 | h3620
                                · rcases p3596_3 (m.d 0 2) (by simp) with h3621 | h3621
                                  · linarith only [h3621, h5, hlam]
                                  · linarith only [h3579, h3621, hlam]
                                · linarith only [h3, h3620, hlam]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3, hlam, p3596_0]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3579, hlam, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3582, hlam, p3596_0]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [h3583, hlam, p3596_1]
                              · have p3596_0 := h3596c.1
                                have p3596_1 := h3596c.2.1
                                have p3596_2 := h3596c.2.2.1
                                have p3596_3 := h3596c.2.2.2
                                linarith only [hlam, p3596_0]
                            · linarith only [h0, h3584, h3591, h3593, h3595, h5, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h3, h3582, h3590, h3594, h4, h5, hlam]
                        · linarith only [h3582, h3591, h3593, h4, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h3580, h3582, h3583, h3584, h3585, h3590, hc23, hc34, hlam, hphi]
                · linarith only [h3579, h3584, h3587, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h3584, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h3582, h3583, h4, h5, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3637 | h3637
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3638 | h3638
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3639 | h3639
              · linarith only [h0, h3579, h3639, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3641 | h3641
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3642 | h3642
                  · linarith only [h1, h3580, h3642, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3644 | h3644
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3645 | h3645
                      · linarith only [h0, h3580, h3638, h3645, h5, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3647 | h3647
                        · linarith only [h1, h3582, h3638, h3647, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3649 | h3649
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3650 | h3650
                            · rcases h0bigk with h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c | h3651c
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [hlam, p3651_0]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h0, h3641, h3647, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                rcases p3651_3 (m.d 0 1) (by simp) with h3654 | h3654
                                · rcases p3651_3 (m.d 0 2) (by simp) with h3655 | h3655
                                  · linarith only [h0, h3655, hlam]
                                  · linarith only [h3655, h4, hlam]
                                · linarith only [h1, h3654, hlam]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h0, h3641, h3647, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                rcases p3651_3 (m.d 0 1) (by simp) with h3660 | h3660
                                · rcases p3651_3 (m.d 0 2) (by simp) with h3661 | h3661
                                  · linarith only [h0, h3661, hlam]
                                  · linarith only [h3579, h3661, hlam]
                                · linarith only [h3, h3660, hlam]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h0, hlam, p3651_0]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [hlam, p3651_0]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h1, h3638, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h5, hlam, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h3645, h5, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h1, hlam, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h4, hlam, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [hlam, p3651_0]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h3580, hlam, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h3582, hlam, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h2, hlam, p3651_0]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h0, h3641, h3647, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h1, h3638, h3645, h5, hc23, hc34, hlam, hphi, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [hlam, p3651_0]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h1, h3582, h3638, h3645, h5, hc23, hc34, hlam, hphi, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h3, hlam, p3651_0]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h3579, hlam, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h1, h3579, h3638, h3645, h5, hc23, hc34, hlam, hphi, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [h3637, hlam, p3651_1]
                              · have p3651_0 := h3651c.1
                                have p3651_1 := h3651c.2.1
                                have p3651_2 := h3651c.2.2.1
                                have p3651_3 := h3651c.2.2.2
                                linarith only [hlam, p3651_0]
                            · linarith only [h0, h3641, h3645, h3649, h3650, h5, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h3641, h3647, h3649, h5, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h3580, h3637, h3638, h3639, h3644, hc23, hc34, hlam, hphi]
                · linarith only [h3579, h3638, h3641, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h3638, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h3579, h3637, h5, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3691 | h3691
      · linarith only [h3691, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3693 | h3693
        · linarith only [h3579, h3693, h4, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3695 | h3695
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3696 | h3696
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3697 | h3697
              · linarith only [h0, h3697, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3699 | h3699
                · linarith only [h0, h3579, h3699, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3701 | h3701
                  · linarith only [h1, h2, h3691, h3693, h3696, h3697, h3701, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3703 | h3703
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3704 | h3704
                      · linarith only [h0, h1, h3691, h3696, h3704, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3706 | h3706
                        · linarith only [h1, h3693, h3696, h3706, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3708 | h3708
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3709 | h3709
                            · rcases h0bigk with h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [hlam, p3710_0]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                rcases p3710_3 (m.d 0 1) (by simp) with h3713 | h3713
                                · rcases p3710_3 (m.d 0 2) (by simp) with h3714 | h3714
                                  · linarith only [h0, h3714, hlam]
                                  · linarith only [h3714, h4, hlam]
                                · linarith only [h1, h3713, hlam]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h2, h3703, hc01, hc45, hlam, hphi, ht0b, ht5b, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h0, h3579, h3696, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h0, hlam, p3710_0]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [hlam, p3710_0]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h1, h3704, h5, hc13, hc34, hlam, hphi, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h5, hlam, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h3579, hlam, p3710_0]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h1, hlam, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h4, hlam, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [hlam, p3710_0]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h3691, hlam, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h3693, hlam, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h2, hlam, p3710_0]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h0, h3696, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h1, h3704, h5, hc13, hc34, hlam, hphi, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [hlam, p3710_0]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h0, h3579, h3696, h3704, h5, hc23, hc34, hlam, hphi, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h3, hlam, p3710_0]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h0, h3696, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h1, h3579, h3704, h3708, hc13, hc34, hlam, hphi, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [h3695, hlam, p3710_1]
                              · have p3710_0 := h3710c.1
                                have p3710_1 := h3710c.2.1
                                have p3710_2 := h3710c.2.2.1
                                have p3710_3 := h3710c.2.2.2
                                linarith only [hlam, p3710_0]
                            · linarith only [h0, h3696, h3704, h3709, h5, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h3696, h3703, h3708, h5, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h3691, h3695, h3696, h3697, h3703, hc23, hc34, hlam, hphi]
            · linarith only [h3696, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3744 | h3744
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3745 | h3745
              · linarith only [h0, h3745, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3747 | h3747
                · linarith only [h0, h3579, h3747, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3749 | h3749
                  · linarith only [h1, h3691, h3749, h4, h5, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3751 | h3751
                    · linarith only [h2, h3695, h3751, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3753 | h3753
                      · linarith only [h0, h1, h3691, h3744, h3753, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3755 | h3755
                        · linarith only [h1, h3693, h3744, h3755, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3757 | h3757
                          · linarith only [h3695, h3753, h3757, h4, h5, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h3744, h3757, h5, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h3744, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 10524000 in
set_option maxHeartbeats 10524000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s3_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  exact r1l7_20_12_14_H_I_L_I_L_I_s4 m hb0 hb2 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 10524000 in
set_option maxHeartbeats 10524000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3761 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h3762 | h3762
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3763 | h3763
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3764 | h3764
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3765 | h3765
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3766 | h3766
          · linarith only [h0, h3761, h3766, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3768 | h3768
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3769 | h3769
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3770 | h3770
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3771 | h3771
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3772 | h3772
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3773 | h3773
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3774 | h3774
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3775 | h3775
                          · rcases h0bigk with h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c | h3776c
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h0, h3768, h3772, h3775, hc01, hc45, hlam, hphi, ht0b, ht5b, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h0, h3768, h3772, h3775, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h3761, h3772, h3775, hc01, hc45, hlam, hphi, ht0b, ht5b, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              rcases p3776_3 (m.d 0 1) (by simp) with h3781 | h3781
                              · rcases p3776_3 (m.d 0 2) (by simp) with h3782 | h3782
                                · linarith only [h0, h3782, hlam]
                                · linarith only [h3762, h3782, hlam]
                              · linarith only [h3, h3781, hlam]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h0, hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h4, hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h2, h3768, h3772, h3775, hc02, hc45, hlam, hphi, ht0b, ht5b, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h1, hlam, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h2, h3768, h3772, h3775, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              rcases p3776_3 (m.d 0 1) (by simp) with h3795 | h3795
                              · rcases p3776_3 (m.d 0 2) (by simp) with h3796 | h3796
                                · linarith only [h3796, h4, hlam]
                                · linarith only [h3762, h3796, hlam]
                              · linarith only [h3, h3795, hlam]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h2, hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h3761, hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h3763, hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h3, h3761, h3769, h3773, h3775, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h3, hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h3762, hlam, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h3764, hlam, p3776_0]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [h3765, hlam, p3776_1]
                            · have p3776_0 := h3776c.1
                              have p3776_1 := h3776c.2.1
                              have p3776_2 := h3776c.2.2.1
                              have p3776_3 := h3776c.2.2.2
                              linarith only [hlam, p3776_0]
                          · linarith only [h0, h3768, h3774, h3775, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3811 | h3811
                          · linarith only [h3772, h3774, h3811, hlam]
                          · rcases h0bigk with h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c | h3813c
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h2, h3761, h3771, h3774, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h2, h3761, h3771, h3772, h3774, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h2, h3771, h3772, h3774, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h3765, h3772, h3774, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h0, hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h4, hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h2, h3771, h3772, h3774, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h3765, h3772, h3774, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h1, hlam, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h2, h3771, h3772, h3774, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h3765, h3772, h3774, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h2, hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h3761, hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h3763, hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h3761, h3765, h3772, h3774, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h3, hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h3762, hlam, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h3764, hlam, p3813_0]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [h3765, hlam, p3813_1]
                            · have p3813_0 := h3813c.1
                              have p3813_1 := h3813c.2.1
                              have p3813_2 := h3813c.2.2.1
                              have p3813_3 := h3813c.2.2.2
                              linarith only [hlam, p3813_0]
                      · linarith only [h3764, h3773, h4, hlam]
                    · linarith only [h3763, h3772, h4, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3841 | h3841
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3842 | h3842
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3843 | h3843
                        · linarith only [h3768, h3771, h3843, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3845 | h3845
                          · linarith only [h3768, h3771, h3841, h3845, hlam]
                          · rcases h0bigk with h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3761, h3765, h3768, h3771, h3841, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3761, h3765, h3768, h3771, h3841, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3765, h3768, h3771, h3841, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3765, h3768, h3771, h3841, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h0, hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h4, hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3765, h3768, h3771, h3841, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h1, hlam, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3765, h3768, h3771, h3841, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3765, h3768, h3771, h3841, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h2, hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3761, hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3763, hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3761, h3765, h3768, h3771, h3841, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3, hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3762, hlam, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3764, hlam, p3847_0]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [h3765, hlam, p3847_1]
                            · have p3847_0 := h3847c.1
                              have p3847_1 := h3847c.2.1
                              have p3847_2 := h3847c.2.2.1
                              have p3847_3 := h3847c.2.2.2
                              linarith only [hlam, p3847_0]
                      · linarith only [h3764, h3842, h4, hlam]
                    · linarith only [h3761, h3765, h3768, h3771, h3841, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h3766, h3768, h3770, hlam]
              · linarith only [h3762, h3768, h3769, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h3761, h3768, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3878 | h3878
          · linarith only [h0, h3761, h3878, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3880 | h3880
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3881 | h3881
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3882 | h3882
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3883 | h3883
                  · linarith only [h2, h3765, h3883, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3885 | h3885
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3886 | h3886
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3887 | h3887
                        · linarith only [h2, h3765, h3880, h3887, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3889 | h3889
                          · linarith only [h2, h3765, h3880, h3885, h3889, hlam]
                          · rcases h0bigk with h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h0, h3881, h3885, h3887, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h0, h3881, h3885, h3887, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              rcases p3891_3 (m.d 0 1) (by simp) with h3895 | h3895
                              · rcases p3891_3 (m.d 0 2) (by simp) with h3896 | h3896
                                · linarith only [h0, h3896, hlam]
                                · linarith only [h3761, h3896, hlam]
                              · linarith only [h2, h3895, hlam]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              rcases p3891_3 (m.d 0 1) (by simp) with h3900 | h3900
                              · rcases p3891_3 (m.d 0 2) (by simp) with h3901 | h3901
                                · linarith only [h0, h3901, hlam]
                                · linarith only [h3762, h3901, hlam]
                              · linarith only [h3, h3900, hlam]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h0, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h4, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h2, h3880, h3885, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h2, h3765, h3880, h3885, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h1, hlam, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h0, h3881, h3885, h3887, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              rcases p3891_3 (m.d 0 1) (by simp) with h3913 | h3913
                              · rcases p3891_3 (m.d 0 2) (by simp) with h3914 | h3914
                                · linarith only [h3914, h4, hlam]
                                · linarith only [h3761, h3914, hlam]
                              · linarith only [h2, h3913, hlam]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              rcases p3891_3 (m.d 0 1) (by simp) with h3918 | h3918
                              · rcases p3891_3 (m.d 0 2) (by simp) with h3919 | h3919
                                · linarith only [h3919, h4, hlam]
                                · linarith only [h3762, h3919, hlam]
                              · linarith only [h3, h3918, hlam]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h2, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3761, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3763, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3765, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3762, hlam, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3764, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h2, h3762, h3880, h3885, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [hlam, p3891_0]
                      · linarith only [h3764, h3886, h4, hlam]
                    · linarith only [h3763, h3885, h4, hlam]
                · linarith only [h3763, h3765, h3878, h3880, h3882, hc24, hc45, hlam, hphi]
              · linarith only [h3762, h3880, h3881, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h3761, h3880, h4, hc12, hc23, hlam, hphi]
      · linarith only [h3762, h3764, h4, hlam]
    · linarith only [h3761, h3763, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3940 | h3940
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3941 | h3941
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3942 | h3942
        · linarith only [h3761, h3762, h3942, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3944 | h3944
          · linarith only [h0, h3944, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3946 | h3946
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3947 | h3947
              · linarith only [h0, h3762, h3947, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3949 | h3949
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3950 | h3950
                  · linarith only [h2, h3942, h3950, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3952 | h3952
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3953 | h3953
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3954 | h3954
                        · linarith only [h2, h3761, h3762, h3942, h3953, h3954, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3956 | h3956
                          · linarith only [h3761, h3762, h3952, h3954, h3956, hlam]
                          · rcases h0bigk with h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h0, h3946, h3952, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3958_1]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h0, h3762, h3941, h3946, h3952, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3958_1]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              rcases p3958_3 (m.d 0 1) (by simp) with h3962 | h3962
                              · rcases p3958_3 (m.d 0 2) (by simp) with h3963 | h3963
                                · linarith only [h0, h3963, hlam]
                                · linarith only [h3761, h3963, hlam]
                              · linarith only [h2, h3962, hlam]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h0, h3762, h3946, h3952, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3958_1]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h0, hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h4, hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h2, h3762, h3953, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3958_1]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h3762, hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h1, hlam, p3958_1]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h0, h3946, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p3958_1]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              rcases p3958_3 (m.d 0 1) (by simp) with h3976 | h3976
                              · rcases p3958_3 (m.d 0 2) (by simp) with h3977 | h3977
                                · linarith only [h3977, h4, hlam]
                                · linarith only [h3761, h3977, hlam]
                              · linarith only [h2, h3976, hlam]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h0, h3762, h3946, h3952, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3958_1]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h2, hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h3761, hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h3940, hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h3942, hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h3, hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h0, h3946, h3952, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p3958_1]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h3941, hlam, p3958_0]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [h2, h3762, h3946, h3952, h3954, hc34, hc45, hlam, hphi, p3958_1]
                            · have p3958_0 := h3958c.1
                              have p3958_1 := h3958c.2.1
                              have p3958_2 := h3958c.2.2.1
                              have p3958_3 := h3958c.2.2.2
                              linarith only [hlam, p3958_0]
                      · linarith only [h3941, h3953, h4, hlam]
                    · linarith only [h0, h3940, h3946, h3952, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h3940, h3942, h3944, h3946, h3949, hc24, hc45, hlam, hphi]
            · linarith only [h3761, h3762, h3946, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3996 | h3996
        · linarith only [h3761, h3941, h3996, h4, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3998 | h3998
          · linarith only [h0, h3761, h3998, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4000 | h4000
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4001 | h4001
              · linarith only [h0, h3762, h4001, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4003 | h4003
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4004 | h4004
                  · linarith only [h2, h3996, h4004, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4006 | h4006
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4007 | h4007
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4008 | h4008
                        · linarith only [h0, h3941, h3996, h4, h4000, h4008, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4010 | h4010
                          · linarith only [h0, h3941, h4, h4000, h4006, h4007, h4008, h4010, hlam]
                          · rcases h0bigk with h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c | h4012c
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h0, h4000, h4006, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h0, h4, h4000, h4006, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              rcases p4012_3 (m.d 0 1) (by simp) with h4016 | h4016
                              · rcases p4012_3 (m.d 0 2) (by simp) with h4017 | h4017
                                · linarith only [h0, h4017, hlam]
                                · linarith only [h3761, h4017, hlam]
                              · linarith only [h2, h4016, hlam]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h0, h3941, h4, h4000, h4006, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h0, hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h4, hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h2, h3941, h4, h4000, h4006, h4007, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h3762, hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h1, hlam, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h3941, h4007, hc02, hc23, hlam, hphi, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h2, h3941, h4000, h4006, h4007, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h3941, hlam, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h2, hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h3761, hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h3940, hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h3996, hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h3, hlam, p4012_0]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h0, h4000, h4006, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h3941, h4007, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [h2, h3941, h4000, h4006, h4007, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4012_1]
                            · have p4012_0 := h4012c.1
                              have p4012_1 := h4012c.2.1
                              have p4012_2 := h4012c.2.2.1
                              have p4012_3 := h4012c.2.2.2
                              linarith only [hlam, p4012_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4042 | h4042
                        · linarith only [h0, h4, h4000, h4007, h4042, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4044 | h4044
                          · linarith only [h0, h4, h4000, h4006, h4007, h4042, h4044, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h4, h4000, h4007, h4044, hc24, hc45, hlam, hphi]
                    · linarith only [h0, h3940, h4, h4000, h4006, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h3940, h3941, h3998, h4000, h4003, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h3761, h4, h4000, hc12, hc23, hlam, hphi]
    · linarith only [h3761, h3940, h4, hlam]

end R2N4
