import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4439 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4562 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h4563 | h4563
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4564 | h4564
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4565 | h4565
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4566 | h4566
        · linarith only [h3333, h4562, h4566, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4568 | h4568
          · linarith only [h4439, h4562, h4566, h4568, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4570 | h4570
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4571 | h4571
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4572 | h4572
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4573 | h4573
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4574 | h4574
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4575 | h4575
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4576 | h4576
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4577 | h4577
                          · rcases h0bigk with h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c | h4578c
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [hlam, p4578_0]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h0, hlam, p4578_1]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h2914, hlam, p4578_0]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h3104, hlam, p4578_1]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h3265, hlam, p4578_1]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h0, h4568, h4574, hc01, hc23, hlam, hphi, ht12, p4578_1]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [hlam, p4578_0]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h3333, hlam, p4578_0]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h4439, hlam, p4578_1]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h0, h4562, h4568, h4574, h4575, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4578_1, u3ehi4]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              rcases p4578_3 (m.d 0 1) (by simp) with h4589 | h4589
                              · linarith only [h2914, h4589, hlam]
                              · rcases p4578_3 (m.d 0 2) (by simp) with h4591 | h4591
                                · linarith only [h3333, h4591, hlam]
                                · linarith only [h0, h4591, hlam]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h3333, h4562, h4575, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4578_1, u3ehi4]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [hlam, p4578_0]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h3333, h4439, h4562, h4575, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4578_1, u3ehi4]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              rcases p4578_3 (m.d 0 1) (by simp) with h4597 | h4597
                              · linarith only [h2914, h4597, hlam]
                              · rcases p4578_3 (m.d 0 2) (by simp) with h4599 | h4599
                                · linarith only [h3333, h4599, hlam]
                                · linarith only [h4562, h4599, hlam]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              rcases p4578_3 (m.d 0 1) (by simp) with h4602 | h4602
                              · linarith only [h3104, h4602, hlam]
                              · rcases p4578_3 (m.d 0 2) (by simp) with h4604 | h4604
                                · linarith only [h4439, h4604, hlam]
                                · linarith only [h0, h4604, hlam]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h4562, h4575, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p4578_1, u3ehi4]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h4563, hlam, p4578_0]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [hlam, p4578_0]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              rcases p4578_3 (m.d 0 1) (by simp) with h4610 | h4610
                              · linarith only [h3104, h4610, hlam]
                              · rcases p4578_3 (m.d 0 2) (by simp) with h4612 | h4612
                                · linarith only [h4439, h4612, hlam]
                                · linarith only [h4562, h4612, hlam]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h0, h4562, h4568, h4574, hc01, hc23, hlam, hphi, ht12, p4578_1]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h4562, hlam, p4578_1]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h4564, hlam, p4578_0]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [h4565, hlam, p4578_1]
                            · have p4578_0 := h4578c.1
                              have p4578_1 := h4578c.2.1
                              have p4578_2 := h4578c.2.2.1
                              have p4578_3 := h4578c.2.2.2
                              linarith only [hlam, p4578_0]
                          · linarith only [h0, h4562, h4568, h4574, h4576, h4577, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h4562, h4568, h4576, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · linarith only [h0, h4562, h4568, h4574, h4575, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h4562, h4566, h4574, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h2914, h3104, h4563, h4565, h4573, hc01, hc13, hlam, hphi]
                · linarith only [h0, h2914, h4562, h4563, h4564, h4565, h4566, h4572, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · linarith only [h2914, h4564, h4571, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h4562, h4570, hlam]
      · linarith only [h4439, h4562, h4565, hlam]
    · linarith only [h4563, h4564, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4630 | h4630
    · linarith only [h4563, h4630, hc34, hlam, hphi, u3ehi4]
    · linarith only [h3333, h4562, h4630, hlam]

end R2N4
