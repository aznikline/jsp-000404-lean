import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 1 2 3 (by decide) (by decide) with h8383 | h8383
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 1 2 3 (by decide) (by decide) with h9450 | h9450
  · rcases m.htr 1 2 4 (by decide) (by decide) with h9451 | h9451
    · rcases m.htr 1 2 5 (by decide) (by decide) with h9452 | h9452
      · rcases m.htr 1 3 4 (by decide) (by decide) with h9453 | h9453
        · rcases m.htr 1 3 5 (by decide) (by decide) with h9454 | h9454
          · rcases m.htr 1 4 5 (by decide) (by decide) with h9455 | h9455
            · rcases m.htr 2 3 4 (by decide) (by decide) with h9456 | h9456
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9457 | h9457
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9458 | h9458
                  · linarith only [h8379, h8382, h9458, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9460 | h9460
                    · linarith only [h6794, h7647, h8378, h8382, h9450, h9456, h9460, hc01, hc12, hlam, hphi]
                    · rcases h1bigk with h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h0, hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h6794, hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h7647, hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h8170, hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        rcases p9462_3 (m.d 0 1) (by simp) with h9468 | h9468
                        · linarith only [h9468, hlam, p9462_0]
                        · rcases p9462_3 (m.d 1 2) (by simp) with h9470 | h9470
                          · rcases p9462_3 (m.d 1 3) (by simp) with h9471 | h9471
                            · linarith only [h9450, h9471, hlam]
                            · linarith only [h6794, h9471, hlam]
                          · linarith only [h9470, hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h6794, hc01, hc12, hlam, hphi, p9462_1]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h7647, h8382, h9455, hc01, hc12, hlam, hphi, p9462_1]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h7647, h8382, h9455, hc01, hc12, hlam, hphi, p9462_1]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        rcases p9462_3 (m.d 0 1) (by simp) with h9479 | h9479
                        · linarith only [h9479, hlam, p9462_0]
                        · rcases p9462_3 (m.d 1 2) (by simp) with h9481 | h9481
                          · rcases p9462_3 (m.d 1 3) (by simp) with h9482 | h9482
                            · rcases p9462_3 (m.d 1 4) (by simp) with h9483 | h9483
                              · linarith only [h9453, h9483, hlam]
                              · linarith only [h7647, h9483, hlam]
                            · linarith only [h9482, hlam, p9462_0]
                          · linarith only [h0, h9481, hlam]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h9450, hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h7647, h8382, h9455, hc01, hc13, hlam, hphi, p9462_1]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h7647, h8382, h9450, h9455, hc01, hc12, hlam, hphi, p9462_1]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        rcases p9462_3 (m.d 0 1) (by simp) with h9492 | h9492
                        · linarith only [h9492, hlam, p9462_0]
                        · rcases p9462_3 (m.d 1 2) (by simp) with h9494 | h9494
                          · rcases p9462_3 (m.d 1 3) (by simp) with h9495 | h9495
                            · rcases p9462_3 (m.d 1 4) (by simp) with h9496 | h9496
                              · rcases p9462_3 (m.d 1 5) (by simp) with h9497 | h9497
                                · linarith only [h9455, h9497, hlam]
                                · linarith only [h8170, h9497, hlam]
                              · linarith only [h9496, hlam, p9462_0]
                            · linarith only [h6794, h9495, hlam]
                          · linarith only [h0, h9494, hlam]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h9451, hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h9453, hlam, p9462_1]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h7647, h8382, h9455, hc01, hc14, hlam, hphi, p9462_1]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        rcases p9462_3 (m.d 0 1) (by simp) with h9507 | h9507
                        · linarith only [h9507, hlam, p9462_0]
                        · rcases p9462_3 (m.d 1 2) (by simp) with h9509 | h9509
                          · rcases p9462_3 (m.d 1 3) (by simp) with h9510 | h9510
                            · rcases p9462_3 (m.d 1 4) (by simp) with h9511 | h9511
                              · rcases p9462_3 (m.d 1 5) (by simp) with h9512 | h9512
                                · rcases h2bigk with h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c | h9513c
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h0, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h0, h9457, hc12, hlam, hphi, ht01, ht0b, ht5b, p9513_1, u5ehi3]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    rcases p9513_3 (m.d 0 2) (by simp) with h9517 | h9517
                                    · rcases p9513_3 (m.d 1 2) (by simp) with h9518 | h9518
                                      · rcases p9513_3 (m.d 2 3) (by simp) with h9519 | h9519
                                        · linarith only [h8378, h9519, hlam]
                                        · linarith only [h9456, h9519, hlam]
                                      · linarith only [h9451, h9518, hlam]
                                    · linarith only [h9517, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    rcases p9513_3 (m.d 0 2) (by simp) with h9524 | h9524
                                    · rcases p9513_3 (m.d 1 2) (by simp) with h9525 | h9525
                                      · rcases p9513_3 (m.d 2 3) (by simp) with h9526 | h9526
                                        · linarith only [h8378, h9526, hlam]
                                        · linarith only [h9457, h9526, hlam]
                                      · linarith only [h9452, h9525, hlam]
                                    · linarith only [h9524, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h8378, h9457, hc12, hlam, hphi, ht01, ht0b, ht5b, p9513_1, u5ehi3]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h9457, hc12, hlam, hphi, ht01, ht0b, ht5b, p9513_1, u5ehi3]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    rcases p9513_3 (m.d 0 2) (by simp) with h9534 | h9534
                                    · linarith only [h0, h9534, hlam]
                                    · linarith only [h8379, h9534, hlam]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    rcases p9513_3 (m.d 0 2) (by simp) with h9537 | h9537
                                    · linarith only [h0, h9537, hlam]
                                    · linarith only [h8380, h9537, hlam]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h8378, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h9450, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    rcases p9513_3 (m.d 0 2) (by simp) with h9543 | h9543
                                    · rcases p9513_3 (m.d 1 2) (by simp) with h9544 | h9544
                                      · rcases p9513_3 (m.d 2 3) (by simp) with h9545 | h9545
                                        · rcases p9513_3 (m.d 2 4) (by simp) with h9546 | h9546
                                          · linarith only [h9456, h9546, hlam]
                                          · rcases p9513_3 (m.d 2 5) (by simp) with h9548 | h9548
                                            · linarith only [h9457, h9548, hlam]
                                            · linarith only [h9458, h9548, hlam]
                                        · linarith only [h9456, h9545, hlam]
                                      · linarith only [h9451, h9544, hlam]
                                    · linarith only [h8379, h9543, hlam]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h8378, h9457, hc02, hlam, hphi, ht0b, ht5b, p9513_1, u5ehi3]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h8379, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h9451, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h9456, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h9458, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h8380, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h9452, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [h9457, hlam, p9513_0]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    rcases p9513_3 (m.d 0 2) (by simp) with h9563 | h9563
                                    · rcases p9513_3 (m.d 1 2) (by simp) with h9564 | h9564
                                      · rcases p9513_3 (m.d 2 3) (by simp) with h9565 | h9565
                                        · rcases p9513_3 (m.d 2 4) (by simp) with h9566 | h9566
                                          · linarith only [h9458, h9566, hlam]
                                          · rcases p9513_3 (m.d 2 5) (by simp) with h9568 | h9568
                                            · rcases h4bigk with h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c | h9569c
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h7647, hlam, p9569_1]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h8382, h9456, hc34, hc45, hlam, hphi, p9569_1]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h8382, hc34, hc45, hlam, hphi, p9569_1]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h8382, hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                rcases p9569_3 (m.d 0 4) (by simp) with h9575 | h9575
                                                · linarith only [h7647, h9575, hlam]
                                                · rcases p9569_3 (m.d 1 4) (by simp) with h9577 | h9577
                                                  · rcases p9569_3 (m.d 2 4) (by simp) with h9578 | h9578
                                                    · linarith only [h9451, h9578, hlam]
                                                    · rcases p9569_3 (m.d 3 4) (by simp) with h9580 | h9580
                                                      · linarith only [h9453, h9580, hlam]
                                                      · rcases p9569_3 (m.d 4 5) (by simp) with h9582 | h9582
                                                        · linarith only [h9455, h9582, hlam]
                                                        · linarith only [h8382, h9582, hlam]
                                                  · linarith only [h7647, h9577, hlam]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h8380, h8382, h9455, hlam, p9513_1, p9569_2]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h8380, h8382, h9455, h9456, hlam, p9513_1, p9569_2]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h8380, h8382, h9450, h9453, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9513_1, p9569_1]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h8379, hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h9451, hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h8380, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p9513_1, p9569_1]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h9458, hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h8381, hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h9453, hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h9456, hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h9460, hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h7647, h9450, h9453, h9455, hc01, hc12, hlam, hphi, p9569_1]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [h9455, hlam, p9569_0]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                rcases p9569_3 (m.d 0 4) (by simp) with h9602 | h9602
                                                · linarith only [h8382, h9602, hlam]
                                                · linarith only [h8379, h9602, hlam]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                rcases p9569_3 (m.d 0 4) (by simp) with h9605 | h9605
                                                · linarith only [h8382, h9605, hlam]
                                                · linarith only [h8381, h9605, hlam]
                                              · have p9569_0 := h9569c.1
                                                have p9569_1 := h9569c.2.1
                                                have p9569_2 := h9569c.2.2.1
                                                have p9569_3 := h9569c.2.2.2
                                                linarith only [hlam, p9569_0]
                                            · linarith only [h9458, h9568, hlam]
                                        · linarith only [h9456, h9565, hlam]
                                      · linarith only [h9451, h9564, hlam]
                                    · linarith only [h8379, h9563, hlam]
                                  · have p9513_0 := h9513c.1
                                    have p9513_1 := h9513c.2.1
                                    have p9513_2 := h9513c.2.2.1
                                    have p9513_3 := h9513c.2.2.2
                                    linarith only [hlam, p9513_0]
                                · linarith only [h9512, hlam, p9462_0]
                              · linarith only [h7647, h9511, hlam]
                            · linarith only [h6794, h9510, hlam]
                          · linarith only [h0, h9509, hlam]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h9452, hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h9454, hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [h9455, hlam, p9462_0]
                      · have p9462_0 := h9462c.1
                        have p9462_1 := h9462c.2.1
                        have p9462_2 := h9462c.2.2.1
                        have p9462_3 := h9462c.2.2.2
                        linarith only [hlam, p9462_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9622 | h9622
                  · linarith only [h8379, h8382, h9622, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9624 | h9624
                    · linarith only [h0, h7647, h8378, h8381, h8382, h9624, hc01, hc12, hlam, hphi]
                    · rcases h1bigk with h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c | h9626c
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h0, hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h6794, hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h7647, hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h8170, hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        rcases p9626_3 (m.d 0 1) (by simp) with h9632 | h9632
                        · linarith only [h9632, hlam, p9626_0]
                        · rcases p9626_3 (m.d 1 2) (by simp) with h9634 | h9634
                          · rcases p9626_3 (m.d 1 3) (by simp) with h9635 | h9635
                            · linarith only [h9450, h9635, hlam]
                            · linarith only [h6794, h9635, hlam]
                          · linarith only [h9634, hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h6794, hc01, hc12, hlam, hphi, p9626_1]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h7647, hc01, hc12, hlam, hphi, p9626_1]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h8170, hc01, hc12, hlam, hphi, p9626_1]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        rcases p9626_3 (m.d 0 1) (by simp) with h9643 | h9643
                        · linarith only [h9643, hlam, p9626_0]
                        · rcases p9626_3 (m.d 1 2) (by simp) with h9645 | h9645
                          · rcases p9626_3 (m.d 1 3) (by simp) with h9646 | h9646
                            · rcases p9626_3 (m.d 1 4) (by simp) with h9647 | h9647
                              · linarith only [h9453, h9647, hlam]
                              · linarith only [h7647, h9647, hlam]
                            · linarith only [h9646, hlam, p9626_0]
                          · linarith only [h0, h9645, hlam]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h9450, hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h9455, h9456, h9457, h9624, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9626_1]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h9450, h9455, h9456, h9457, h9624, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9626_1]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        rcases p9626_3 (m.d 0 1) (by simp) with h9656 | h9656
                        · linarith only [h9656, hlam, p9626_0]
                        · rcases p9626_3 (m.d 1 2) (by simp) with h9658 | h9658
                          · rcases p9626_3 (m.d 1 3) (by simp) with h9659 | h9659
                            · rcases p9626_3 (m.d 1 4) (by simp) with h9660 | h9660
                              · rcases p9626_3 (m.d 1 5) (by simp) with h9661 | h9661
                                · linarith only [h9455, h9661, hlam]
                                · linarith only [h8170, h9661, hlam]
                              · linarith only [h9660, hlam, p9626_0]
                            · linarith only [h6794, h9659, hlam]
                          · linarith only [h0, h9658, hlam]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h9451, hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h9453, hlam, p9626_1]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h9455, h9456, h9457, h9624, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9626_1]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        rcases p9626_3 (m.d 0 1) (by simp) with h9671 | h9671
                        · linarith only [h9671, hlam, p9626_0]
                        · rcases p9626_3 (m.d 1 2) (by simp) with h9673 | h9673
                          · rcases p9626_3 (m.d 1 3) (by simp) with h9674 | h9674
                            · rcases p9626_3 (m.d 1 4) (by simp) with h9675 | h9675
                              · rcases p9626_3 (m.d 1 5) (by simp) with h9676 | h9676
                                · rcases h2bigk with h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c | h9677c
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h0, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    rcases p9677_3 (m.d 0 2) (by simp) with h9680 | h9680
                                    · rcases p9677_3 (m.d 1 2) (by simp) with h9681 | h9681
                                      · rcases p9677_3 (m.d 2 3) (by simp) with h9682 | h9682
                                        · linarith only [h9682, hlam, p9677_0]
                                        · rcases p9677_3 (m.d 2 4) (by simp) with h9684 | h9684
                                          · linarith only [h8379, h9684, hlam]
                                          · rcases p9677_3 (m.d 2 5) (by simp) with h9686 | h9686
                                            · linarith only [h8380, h9686, hlam]
                                            · linarith only [h9457, h9686, hlam]
                                      · linarith only [h9450, h9681, hlam]
                                    · linarith only [h9680, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    rcases p9677_3 (m.d 0 2) (by simp) with h9691 | h9691
                                    · rcases p9677_3 (m.d 1 2) (by simp) with h9692 | h9692
                                      · rcases p9677_3 (m.d 2 3) (by simp) with h9693 | h9693
                                        · linarith only [h8378, h9693, hlam]
                                        · linarith only [h9456, h9693, hlam]
                                      · linarith only [h9451, h9692, hlam]
                                    · linarith only [h9691, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    rcases p9677_3 (m.d 0 2) (by simp) with h9698 | h9698
                                    · rcases p9677_3 (m.d 1 2) (by simp) with h9699 | h9699
                                      · rcases p9677_3 (m.d 2 3) (by simp) with h9700 | h9700
                                        · linarith only [h8378, h9700, hlam]
                                        · rcases p9677_3 (m.d 2 4) (by simp) with h9702 | h9702
                                          · linarith only [h8379, h9702, hlam]
                                          · rcases p9677_3 (m.d 2 5) (by simp) with h9704 | h9704
                                            · linarith only [h9704, hlam, p9677_0]
                                            · rcases h4bigk with h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h7647, hlam, p9706_1]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h8382, hc24, hc45, hlam, hphi, p9706_1]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h8382, hc34, hc45, hlam, hphi, p9706_1]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h8382, hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                rcases p9706_3 (m.d 0 4) (by simp) with h9712 | h9712
                                                · linarith only [h7647, h9712, hlam]
                                                · rcases p9706_3 (m.d 1 4) (by simp) with h9714 | h9714
                                                  · rcases p9706_3 (m.d 2 4) (by simp) with h9715 | h9715
                                                    · linarith only [h9451, h9715, hlam]
                                                    · rcases p9706_3 (m.d 3 4) (by simp) with h9717 | h9717
                                                      · linarith only [h9453, h9717, hlam]
                                                      · rcases p9706_3 (m.d 4 5) (by simp) with h9719 | h9719
                                                        · linarith only [h9455, h9719, hlam]
                                                        · linarith only [h8382, h9719, hlam]
                                                  · linarith only [h7647, h9714, hlam]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                rcases p9706_3 (m.d 0 4) (by simp) with h9724 | h9724
                                                · linarith only [h7647, h9724, hlam]
                                                · linarith only [h8379, h9724, hlam]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h9455, h9456, h9457, h9624, hlam, p9706_2]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h7647, h8382, hc01, hc14, hlam, hphi, p9706_1]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h8379, hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h9451, hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h8379, h8382, hc34, hc45, hlam, hphi, p9706_1]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h9622, hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h8381, hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h9453, hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h9456, hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h9624, hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h7647, h9450, h9453, h9455, hc01, hc12, hlam, hphi, p9706_1]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [h9455, hlam, p9706_0]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                rcases p9706_3 (m.d 0 4) (by simp) with h9741 | h9741
                                                · linarith only [h8382, h9741, hlam]
                                                · linarith only [h8379, h9741, hlam]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                rcases p9706_3 (m.d 0 4) (by simp) with h9744 | h9744
                                                · linarith only [h8382, h9744, hlam]
                                                · linarith only [h8381, h9744, hlam]
                                              · have p9706_0 := h9706c.1
                                                have p9706_1 := h9706c.2.1
                                                have p9706_2 := h9706c.2.2.1
                                                have p9706_3 := h9706c.2.2.2
                                                linarith only [hlam, p9706_0]
                                      · linarith only [h9452, h9699, hlam]
                                    · linarith only [h9698, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h8380, hc12, hlam, hphi, ht01, ht0b, ht5b, p9677_1, u5ehi2]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    rcases p9677_3 (m.d 0 2) (by simp) with h9752 | h9752
                                    · linarith only [h0, h9752, hlam]
                                    · linarith only [h8378, h9752, hlam]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    rcases p9677_3 (m.d 0 2) (by simp) with h9755 | h9755
                                    · linarith only [h0, h9755, hlam]
                                    · linarith only [h8379, h9755, hlam]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    rcases p9677_3 (m.d 0 2) (by simp) with h9758 | h9758
                                    · linarith only [h0, h9758, hlam]
                                    · linarith only [h8380, h9758, hlam]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h8378, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h9450, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h9450, h9453, h9455, h9456, h9457, h9624, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9677_1]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h9457, hlam, p9677_1]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h8379, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h9451, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h9456, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h9622, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h8380, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h9452, hlam, p9677_0]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [h8380, h8382, h9450, h9453, h9455, h9456, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9677_1]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    rcases p9677_3 (m.d 0 2) (by simp) with h9774 | h9774
                                    · rcases p9677_3 (m.d 1 2) (by simp) with h9775 | h9775
                                      · rcases p9677_3 (m.d 2 3) (by simp) with h9776 | h9776
                                        · linarith only [h9457, h9776, hlam]
                                        · linarith only [h9456, h9776, hlam]
                                      · linarith only [h9451, h9775, hlam]
                                    · linarith only [h8379, h9774, hlam]
                                  · have p9677_0 := h9677c.1
                                    have p9677_1 := h9677c.2.1
                                    have p9677_2 := h9677c.2.2.1
                                    have p9677_3 := h9677c.2.2.2
                                    linarith only [hlam, p9677_0]
                                · linarith only [h9676, hlam, p9626_0]
                              · linarith only [h7647, h9675, hlam]
                            · linarith only [h6794, h9674, hlam]
                          · linarith only [h0, h9673, hlam]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h9452, hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h9454, hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [h9455, hlam, p9626_0]
                      · have p9626_0 := h9626c.1
                        have p9626_1 := h9626c.2.1
                        have p9626_2 := h9626c.2.2.1
                        have p9626_3 := h9626c.2.2.2
                        linarith only [hlam, p9626_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9790 | h9790
                · linarith only [h8381, h8382, h9450, h9453, h9455, h9456, h9790, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9792 | h9792
                  · linarith only [h0, h8379, h8381, h8382, h9456, h9792, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9794 | h9794
                    · linarith only [h8381, h8382, h9794, hlam]
                    · rcases h1bigk with h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h0, hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h6794, hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h7647, hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h8170, hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        rcases p9796_3 (m.d 0 1) (by simp) with h9802 | h9802
                        · linarith only [h9802, hlam, p9796_0]
                        · rcases p9796_3 (m.d 1 2) (by simp) with h9804 | h9804
                          · rcases p9796_3 (m.d 1 3) (by simp) with h9805 | h9805
                            · linarith only [h9450, h9805, hlam]
                            · linarith only [h6794, h9805, hlam]
                          · linarith only [h9804, hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h6794, hc01, hc12, hlam, hphi, p9796_1]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h7647, hc01, hc12, hlam, hphi, p9796_1]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h8170, hc01, hc12, hlam, hphi, p9796_1]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        rcases p9796_3 (m.d 0 1) (by simp) with h9813 | h9813
                        · linarith only [h9813, hlam, p9796_0]
                        · rcases p9796_3 (m.d 1 2) (by simp) with h9815 | h9815
                          · rcases p9796_3 (m.d 1 3) (by simp) with h9816 | h9816
                            · rcases p9796_3 (m.d 1 4) (by simp) with h9817 | h9817
                              · linarith only [h9453, h9817, hlam]
                              · linarith only [h7647, h9817, hlam]
                            · linarith only [h9816, hlam, p9796_0]
                          · linarith only [h0, h9815, hlam]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h9450, hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h8381, h8382, h9455, h9456, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9796_1]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h8381, h8382, h9450, h9455, h9456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9796_1]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        rcases p9796_3 (m.d 0 1) (by simp) with h9826 | h9826
                        · linarith only [h9826, hlam, p9796_0]
                        · rcases p9796_3 (m.d 1 2) (by simp) with h9828 | h9828
                          · rcases p9796_3 (m.d 1 3) (by simp) with h9829 | h9829
                            · rcases p9796_3 (m.d 1 4) (by simp) with h9830 | h9830
                              · rcases p9796_3 (m.d 1 5) (by simp) with h9831 | h9831
                                · linarith only [h9455, h9831, hlam]
                                · linarith only [h8170, h9831, hlam]
                              · linarith only [h9830, hlam, p9796_0]
                            · linarith only [h6794, h9829, hlam]
                          · linarith only [h0, h9828, hlam]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h9451, hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h9453, hlam, p9796_1]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h8381, h8382, h9455, h9456, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9796_1]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        rcases p9796_3 (m.d 0 1) (by simp) with h9841 | h9841
                        · linarith only [h9841, hlam, p9796_0]
                        · rcases p9796_3 (m.d 1 2) (by simp) with h9843 | h9843
                          · rcases p9796_3 (m.d 1 3) (by simp) with h9844 | h9844
                            · rcases p9796_3 (m.d 1 4) (by simp) with h9845 | h9845
                              · rcases p9796_3 (m.d 1 5) (by simp) with h9846 | h9846
                                · rcases h2bigk with h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c | h9847c
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h0, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    rcases p9847_3 (m.d 0 2) (by simp) with h9850 | h9850
                                    · rcases p9847_3 (m.d 1 2) (by simp) with h9851 | h9851
                                      · rcases p9847_3 (m.d 2 3) (by simp) with h9852 | h9852
                                        · linarith only [h9852, hlam, p9847_0]
                                        · rcases p9847_3 (m.d 2 4) (by simp) with h9854 | h9854
                                          · linarith only [h8379, h9854, hlam]
                                          · linarith only [h9456, h9854, hlam]
                                      · linarith only [h9450, h9851, hlam]
                                    · linarith only [h9850, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    rcases p9847_3 (m.d 0 2) (by simp) with h9859 | h9859
                                    · rcases p9847_3 (m.d 1 2) (by simp) with h9860 | h9860
                                      · rcases p9847_3 (m.d 2 3) (by simp) with h9861 | h9861
                                        · linarith only [h8378, h9861, hlam]
                                        · rcases p9847_3 (m.d 2 4) (by simp) with h9863 | h9863
                                          · linarith only [h9863, hlam, p9847_0]
                                          · rcases p9847_3 (m.d 2 5) (by simp) with h9865 | h9865
                                            · linarith only [h8380, h9865, hlam]
                                            · linarith only [h9792, h9865, hlam]
                                      · linarith only [h9451, h9860, hlam]
                                    · linarith only [h9859, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    rcases p9847_3 (m.d 0 2) (by simp) with h9870 | h9870
                                    · rcases p9847_3 (m.d 1 2) (by simp) with h9871 | h9871
                                      · rcases p9847_3 (m.d 2 3) (by simp) with h9872 | h9872
                                        · linarith only [h8378, h9872, hlam]
                                        · rcases p9847_3 (m.d 2 4) (by simp) with h9874 | h9874
                                          · linarith only [h8379, h9874, hlam]
                                          · rcases p9847_3 (m.d 2 5) (by simp) with h9876 | h9876
                                            · linarith only [h9876, hlam, p9847_0]
                                            · rcases h4bigk with h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h7647, hlam, p9878_1]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h8382, hc24, hc45, hlam, hphi, p9878_1]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h8382, h9456, hc23, hc45, hlam, hphi, ht34, p9878_1]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h8382, hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                rcases p9878_3 (m.d 0 4) (by simp) with h9884 | h9884
                                                · linarith only [h7647, h9884, hlam]
                                                · rcases p9878_3 (m.d 1 4) (by simp) with h9886 | h9886
                                                  · rcases p9878_3 (m.d 2 4) (by simp) with h9887 | h9887
                                                    · linarith only [h9451, h9887, hlam]
                                                    · rcases p9878_3 (m.d 3 4) (by simp) with h9889 | h9889
                                                      · linarith only [h9453, h9889, hlam]
                                                      · rcases p9878_3 (m.d 4 5) (by simp) with h9891 | h9891
                                                        · linarith only [h9455, h9891, hlam]
                                                        · linarith only [h8382, h9891, hlam]
                                                  · linarith only [h7647, h9886, hlam]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                rcases p9878_3 (m.d 0 4) (by simp) with h9896 | h9896
                                                · linarith only [h7647, h9896, hlam]
                                                · linarith only [h8379, h9896, hlam]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                rcases p9878_3 (m.d 0 4) (by simp) with h9899 | h9899
                                                · linarith only [h7647, h9899, hlam]
                                                · linarith only [h8381, h9899, hlam]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h7647, h8382, h9450, h9453, hc01, hc12, hlam, hphi, p9878_1]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h8379, hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h9451, hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h9456, hlam, p9878_1]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h9792, hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h8381, hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h9453, hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h8381, h8382, hc24, hc45, hlam, hphi, p9878_1]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h9794, hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h7647, h9450, h9453, h9455, hc01, hc12, hlam, hphi, p9878_1]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h9455, hlam, p9878_0]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                rcases p9878_3 (m.d 0 4) (by simp) with h9915 | h9915
                                                · linarith only [h8382, h9915, hlam]
                                                · linarith only [h8379, h9915, hlam]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [h9450, h9453, h9455, h9456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9878_1]
                                              · have p9878_0 := h9878c.1
                                                have p9878_1 := h9878c.2.1
                                                have p9878_2 := h9878c.2.2.1
                                                have p9878_3 := h9878c.2.2.2
                                                linarith only [hlam, p9878_0]
                                      · linarith only [h9452, h9871, hlam]
                                    · linarith only [h9870, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h8378, h8381, h9456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9847_1]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h8381, h8382, h9450, h9453, h9455, h9456, hlam, p9847_2]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    rcases p9847_3 (m.d 0 2) (by simp) with h9925 | h9925
                                    · linarith only [h0, h9925, hlam]
                                    · linarith only [h8379, h9925, hlam]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    rcases p9847_3 (m.d 0 2) (by simp) with h9928 | h9928
                                    · linarith only [h0, h9928, hlam]
                                    · linarith only [h8380, h9928, hlam]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h8378, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h9450, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h9456, hlam, p9847_1]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h9790, hlam, p9847_1]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h8379, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h9451, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h8379, h8382, h9450, h9453, h9455, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9847_1]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h9792, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h8380, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [h9452, hlam, p9847_0]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    rcases p9847_3 (m.d 0 2) (by simp) with h9943 | h9943
                                    · rcases p9847_3 (m.d 1 2) (by simp) with h9944 | h9944
                                      · rcases p9847_3 (m.d 2 3) (by simp) with h9945 | h9945
                                        · linarith only [h9790, h9945, hlam]
                                        · rcases p9847_3 (m.d 2 4) (by simp) with h9947 | h9947
                                          · linarith only [h9792, h9947, hlam]
                                          · linarith only [h9456, h9947, hlam]
                                      · linarith only [h9450, h9944, hlam]
                                    · linarith only [h8378, h9943, hlam]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    rcases p9847_3 (m.d 0 2) (by simp) with h9952 | h9952
                                    · rcases p9847_3 (m.d 1 2) (by simp) with h9953 | h9953
                                      · rcases p9847_3 (m.d 2 3) (by simp) with h9954 | h9954
                                        · linarith only [h9790, h9954, hlam]
                                        · rcases p9847_3 (m.d 2 4) (by simp) with h9956 | h9956
                                          · linarith only [h9792, h9956, hlam]
                                          · rcases p9847_3 (m.d 2 5) (by simp) with h9958 | h9958
                                            · rcases h4bigk with h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c | h9959c
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h7647, hlam, p9959_1]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h8382, h9450, h9453, h9455, h9456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9959_1]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h8382, h9450, h9453, h9455, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9959_1]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h8382, hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                rcases p9959_3 (m.d 0 4) (by simp) with h9965 | h9965
                                                · linarith only [h7647, h9965, hlam]
                                                · rcases p9959_3 (m.d 1 4) (by simp) with h9967 | h9967
                                                  · rcases p9959_3 (m.d 2 4) (by simp) with h9968 | h9968
                                                    · linarith only [h9451, h9968, hlam]
                                                    · rcases p9959_3 (m.d 3 4) (by simp) with h9970 | h9970
                                                      · linarith only [h9453, h9970, hlam]
                                                      · rcases p9959_3 (m.d 4 5) (by simp) with h9972 | h9972
                                                        · linarith only [h9455, h9972, hlam]
                                                        · linarith only [h8382, h9972, hlam]
                                                  · linarith only [h7647, h9967, hlam]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h8380, h8382, h9455, hlam, p9847_1, p9959_2]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                rcases p9959_3 (m.d 0 4) (by simp) with h9978 | h9978
                                                · linarith only [h7647, h9978, hlam]
                                                · linarith only [h8381, h9978, hlam]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h8380, h8382, h9456, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9847_1, p9959_1]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h8379, hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h9451, hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h9456, hlam, p9959_1]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h9792, hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h8381, hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h9453, hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h8381, h8382, h9456, hc23, hc45, hlam, hphi, ht34, p9959_1]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h9794, hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h7647, h9450, h9453, h9455, hc01, hc12, hlam, hphi, p9959_1]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h9455, hlam, p9959_0]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                rcases p9959_3 (m.d 0 4) (by simp) with h9994 | h9994
                                                · linarith only [h8382, h9994, hlam]
                                                · linarith only [h8379, h9994, hlam]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [h9450, h9453, h9455, h9456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9959_1]
                                              · have p9959_0 := h9959c.1
                                                have p9959_1 := h9959c.2.1
                                                have p9959_2 := h9959c.2.2.1
                                                have p9959_3 := h9959c.2.2.2
                                                linarith only [hlam, p9959_0]
                                            · linarith only [h9792, h9958, hlam]
                                      · linarith only [h9451, h9953, hlam]
                                    · linarith only [h8379, h9952, hlam]
                                  · have p9847_0 := h9847c.1
                                    have p9847_1 := h9847c.2.1
                                    have p9847_2 := h9847c.2.2.1
                                    have p9847_3 := h9847c.2.2.2
                                    linarith only [hlam, p9847_0]
                                · linarith only [h9846, hlam, p9796_0]
                              · linarith only [h7647, h9845, hlam]
                            · linarith only [h6794, h9844, hlam]
                          · linarith only [h0, h9843, hlam]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h9452, hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h9454, hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [h9455, hlam, p9796_0]
                      · have p9796_0 := h9796c.1
                        have p9796_1 := h9796c.2.1
                        have p9796_2 := h9796c.2.2.1
                        have p9796_3 := h9796c.2.2.2
                        linarith only [hlam, p9796_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h10011 | h10011
              · rcases m.htr 2 3 5 (by decide) (by decide) with h10012 | h10012
                · rcases m.htr 2 4 5 (by decide) (by decide) with h10013 | h10013
                  · linarith only [h10013, h7647, h9455, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10015 | h10015
                    · linarith only [h10011, h10015, h7647, h8378, h9455, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c | h10017c
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h0, hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h6794, hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h7647, hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h8170, hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        rcases p10017_3 (m.d 0 1) (by simp) with h10023 | h10023
                        · linarith only [h10023, hlam, p10017_0]
                        · rcases p10017_3 (m.d 1 2) (by simp) with h10025 | h10025
                          · rcases p10017_3 (m.d 1 3) (by simp) with h10026 | h10026
                            · linarith only [h10026, h9450, hlam]
                            · linarith only [h10026, h6794, hlam]
                          · linarith only [h10025, hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h6794, hc01, hc12, hlam, hphi, p10017_1]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h7647, hc01, hc12, hlam, hphi, p10017_1]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h8170, hc01, hc12, hlam, hphi, p10017_1]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        rcases p10017_3 (m.d 0 1) (by simp) with h10034 | h10034
                        · linarith only [h10034, hlam, p10017_0]
                        · rcases p10017_3 (m.d 1 2) (by simp) with h10036 | h10036
                          · rcases p10017_3 (m.d 1 3) (by simp) with h10037 | h10037
                            · rcases p10017_3 (m.d 1 4) (by simp) with h10038 | h10038
                              · linarith only [h10038, h9453, hlam]
                              · linarith only [h10038, h7647, hlam]
                            · linarith only [h10037, hlam, p10017_0]
                          · linarith only [h0, h10036, hlam]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h9450, hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h7647, hc01, hc13, hlam, hphi, p10017_1]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h8170, h9450, hc01, hc12, hlam, hphi, p10017_1]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h9455, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10017_1]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h9451, hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h9453, hlam, p10017_1]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h9455, hlam, p10017_1]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        rcases p10017_3 (m.d 0 1) (by simp) with h10052 | h10052
                        · linarith only [h10052, hlam, p10017_0]
                        · rcases p10017_3 (m.d 1 2) (by simp) with h10054 | h10054
                          · rcases p10017_3 (m.d 1 3) (by simp) with h10055 | h10055
                            · rcases p10017_3 (m.d 1 4) (by simp) with h10056 | h10056
                              · linarith only [h10056, h9455, hlam]
                              · linarith only [h10056, h7647, hlam]
                            · linarith only [h10055, h6794, hlam]
                          · linarith only [h0, h10054, hlam]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h9452, hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h9454, hlam, p10017_0]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [h7647, hc01, hc15, hlam, hphi, p10017_1]
                      · have p10017_0 := h10017c.1
                        have p10017_1 := h10017c.2.1
                        have p10017_2 := h10017c.2.2.1
                        have p10017_3 := h10017c.2.2.2
                        linarith only [hlam, p10017_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h10065 | h10065
                  · linarith only [h10011, h10012, h10065, h8170, h9450, h9454, h9455, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10067 | h10067
                    · linarith only [h10067, h7647, h9455, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases h1bigk with h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h0, hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h6794, hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h7647, hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h8170, hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        rcases p10069_3 (m.d 0 1) (by simp) with h10075 | h10075
                        · linarith only [h10075, hlam, p10069_0]
                        · rcases p10069_3 (m.d 1 2) (by simp) with h10077 | h10077
                          · rcases p10069_3 (m.d 1 3) (by simp) with h10078 | h10078
                            · linarith only [h10078, h9450, hlam]
                            · linarith only [h10078, h6794, hlam]
                          · linarith only [h10077, hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h10012, h9454, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10069_1]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h7647, hc01, hc12, hlam, hphi, p10069_1]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h8170, hc01, hc12, hlam, hphi, p10069_1]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        rcases p10069_3 (m.d 0 1) (by simp) with h10086 | h10086
                        · linarith only [h10086, hlam, p10069_0]
                        · rcases p10069_3 (m.d 1 2) (by simp) with h10088 | h10088
                          · rcases p10069_3 (m.d 1 3) (by simp) with h10089 | h10089
                            · rcases p10069_3 (m.d 1 4) (by simp) with h10090 | h10090
                              · linarith only [h10090, h9453, hlam]
                              · linarith only [h10090, h7647, hlam]
                            · linarith only [h10089, hlam, p10069_0]
                          · linarith only [h0, h10088, hlam]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h9450, hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h7647, hc01, hc13, hlam, hphi, p10069_1]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h10011, h10012, h9450, h9454, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10069_1]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h9455, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10069_1]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h9451, hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h9453, hlam, p10069_1]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h9455, hlam, p10069_1]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        rcases p10069_3 (m.d 0 1) (by simp) with h10104 | h10104
                        · linarith only [h10104, hlam, p10069_0]
                        · rcases p10069_3 (m.d 1 2) (by simp) with h10106 | h10106
                          · rcases p10069_3 (m.d 1 3) (by simp) with h10107 | h10107
                            · rcases p10069_3 (m.d 1 4) (by simp) with h10108 | h10108
                              · linarith only [h10108, h9455, hlam]
                              · linarith only [h10108, h7647, hlam]
                            · linarith only [h10107, h6794, hlam]
                          · linarith only [h0, h10106, hlam]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h9452, hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h9454, hlam, p10069_0]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [h7647, hc01, hc15, hlam, hphi, p10069_1]
                      · have p10069_0 := h10069c.1
                        have p10069_1 := h10069c.2.1
                        have p10069_2 := h10069c.2.2.1
                        have p10069_3 := h10069c.2.2.2
                        linarith only [hlam, p10069_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h10117 | h10117
                · linarith only [h10011, h10117, h8381, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h10119 | h10119
                  · linarith only [h0, h10119, h8170, h8379, h9455, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10121 | h10121
                    · linarith only [h10121, h7647, h8381, h9455, hlam]
                    · rcases h1bigk with h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c | h10123c
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h0, hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h6794, hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h7647, hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h8170, hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        rcases p10123_3 (m.d 0 1) (by simp) with h10129 | h10129
                        · linarith only [h10129, hlam, p10123_0]
                        · rcases p10123_3 (m.d 1 2) (by simp) with h10131 | h10131
                          · rcases p10123_3 (m.d 1 3) (by simp) with h10132 | h10132
                            · linarith only [h10132, h9450, hlam]
                            · linarith only [h10132, h6794, hlam]
                          · linarith only [h10131, hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h6794, hc01, hc12, hlam, hphi, p10123_1]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h7647, hc01, hc12, hlam, hphi, p10123_1]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h8170, hc01, hc12, hlam, hphi, p10123_1]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        rcases p10123_3 (m.d 0 1) (by simp) with h10140 | h10140
                        · linarith only [h10140, hlam, p10123_0]
                        · rcases p10123_3 (m.d 1 2) (by simp) with h10142 | h10142
                          · rcases p10123_3 (m.d 1 3) (by simp) with h10143 | h10143
                            · rcases p10123_3 (m.d 1 4) (by simp) with h10144 | h10144
                              · linarith only [h10144, h9453, hlam]
                              · linarith only [h10144, h7647, hlam]
                            · linarith only [h10143, hlam, p10123_0]
                          · linarith only [h0, h10142, hlam]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h9450, hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h7647, hc01, hc13, hlam, hphi, p10123_1]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h7647, h9450, h9455, hc01, hc12, hlam, hphi, p10123_1]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h9455, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10123_1]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h9451, hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h9453, hlam, p10123_1]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h9455, hlam, p10123_1]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        rcases p10123_3 (m.d 0 1) (by simp) with h10158 | h10158
                        · linarith only [h10158, hlam, p10123_0]
                        · rcases p10123_3 (m.d 1 2) (by simp) with h10160 | h10160
                          · rcases p10123_3 (m.d 1 3) (by simp) with h10161 | h10161
                            · rcases p10123_3 (m.d 1 4) (by simp) with h10162 | h10162
                              · linarith only [h10162, h9455, hlam]
                              · linarith only [h10162, h7647, hlam]
                            · linarith only [h10161, h6794, hlam]
                          · linarith only [h0, h10160, hlam]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h9452, hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h9454, hlam, p10123_0]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [h7647, hc01, hc15, hlam, hphi, p10123_1]
                      · have p10123_0 := h10123c.1
                        have p10123_1 := h10123c.2.1
                        have p10123_2 := h10123c.2.2.1
                        have p10123_3 := h10123c.2.2.2
                        linarith only [hlam, p10123_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h10171 | h10171
            · linarith only [h10171, h7647, h8382, h9453, h9454, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h10173 | h10173
              · rcases m.htr 2 3 5 (by decide) (by decide) with h10174 | h10174
                · linarith only [h10174, h6794, h9454, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h10176 | h10176
                  · linarith only [h10171, h10176, h7647, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10178 | h10178
                    · linarith only [h10171, h10173, h10178, h7647, h8378, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h0, hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h6794, hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h7647, hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h8170, hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        rcases p10180_3 (m.d 0 1) (by simp) with h10186 | h10186
                        · linarith only [h10186, hlam, p10180_0]
                        · rcases p10180_3 (m.d 1 2) (by simp) with h10188 | h10188
                          · rcases p10180_3 (m.d 1 3) (by simp) with h10189 | h10189
                            · linarith only [h10189, h9450, hlam]
                            · linarith only [h10189, h6794, hlam]
                          · linarith only [h10188, hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h6794, hc01, hc12, hlam, hphi, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h7647, hc01, hc12, hlam, hphi, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h8170, hc01, hc12, hlam, hphi, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h10178, h9454, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h9450, hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h7647, hc01, hc13, hlam, hphi, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h9454, hlam, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h10178, h9453, h9454, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h9451, hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h9453, hlam, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h10171, hlam, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        rcases p10180_3 (m.d 0 1) (by simp) with h10207 | h10207
                        · linarith only [h10207, hlam, p10180_0]
                        · rcases p10180_3 (m.d 1 2) (by simp) with h10209 | h10209
                          · rcases p10180_3 (m.d 1 3) (by simp) with h10210 | h10210
                            · linarith only [h10210, h9454, hlam]
                            · linarith only [h10210, h6794, hlam]
                          · linarith only [h0, h10209, hlam]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h9452, hlam, p10180_0]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h6794, hc01, hc15, hlam, hphi, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [h7647, hc01, hc15, hlam, hphi, p10180_1]
                      · have p10180_0 := h10180c.1
                        have p10180_1 := h10180c.2.1
                        have p10180_2 := h10180c.2.2.1
                        have p10180_3 := h10180c.2.2.2
                        linarith only [hlam, p10180_0]
              · linarith only [h10173, h6794, h8381, h9454, hc23, hc35, hlam, hphi]
        · linarith only [h6794, h8381, h9453, hlam]
      · linarith only [h0, h8380, h9452, hlam]
    · linarith only [h0, h8379, h8380, h8382, h9451, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
  · linarith only [h0, h8378, h9450, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 0 4 5 (by decide) (by decide) with h8382 | h8382
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382

end R2N4
