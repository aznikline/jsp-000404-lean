import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x1_x1_x1 (m : N7Model)
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
    (h4562 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h4633 | h4633
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4634 | h4634
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4635 | h4635
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4636 | h4636
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4637 | h4637
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4638 | h4638
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4639 | h4639
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4640 | h4640
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4641 | h4641
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4642 | h4642
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4643 | h4643
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4644 | h4644
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4645 | h4645
                          · linarith only [h3333, h4633, h4636, h4645, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h4439, h4635, h4636, h4642, h4645, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h4439, h4635, h4644, hlam]
                      · linarith only [h3333, h4633, h4643, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3333, h4633, h4642, hlam]
                  · linarith only [h3104, h4439, h4635, h4641, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h3333, h4439, h4634, h4636, h4637, h4639, h4640, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h3333, h4633, h4636, h4639, hlam]
            · linarith only [h3333, h4633, h4636, h4638, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h3333, h4633, h4636, h4637, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4656 | h4656
          · linarith only [h4439, h4636, h4656, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4658 | h4658
            · linarith only [h0, h4562, h4636, h4658, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4660 | h4660
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4661 | h4661
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4662 | h4662
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4663 | h4663
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4664 | h4664
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4665 | h4665
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4666 | h4666
                          · rcases h0bigk with h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [hlam, p4667_0]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h0, hlam, p4667_1]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h2914, hlam, p4667_0]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h3104, hlam, p4667_1]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h3265, hlam, p4667_1]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h0, h4658, h4663, h4665, hc01, hc23, hlam, hphi, ht12, p4667_1]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [hlam, p4667_0]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h3333, hlam, p4667_0]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h4439, hlam, p4667_1]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h4562, hlam, p4667_0]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              rcases p4667_3 (m.d 0 1) (by simp) with h4678 | h4678
                              · linarith only [h2914, h4678, hlam]
                              · rcases p4667_3 (m.d 0 2) (by simp) with h4680 | h4680
                                · linarith only [h3333, h4680, hlam]
                                · linarith only [h0, h4680, hlam]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              rcases p4667_3 (m.d 0 1) (by simp) with h4683 | h4683
                              · linarith only [h2914, h4683, hlam]
                              · rcases p4667_3 (m.d 0 2) (by simp) with h4685 | h4685
                                · linarith only [h3333, h4685, hlam]
                                · rcases p4667_3 (m.d 0 3) (by simp) with h4687 | h4687
                                  · rcases p4667_3 (m.d 0 4) (by simp) with h4688 | h4688
                                    · linarith only [h4633, h4688, hlam]
                                    · linarith only [h4439, h4688, hlam]
                                  · linarith only [h3333, h4687, hlam]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [hlam, p4667_0]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h2914, h4633, h4636, h4666, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4667_1, u5ehi4]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              rcases p4667_3 (m.d 0 1) (by simp) with h4694 | h4694
                              · linarith only [h2914, h4694, hlam]
                              · rcases p4667_3 (m.d 0 2) (by simp) with h4696 | h4696
                                · linarith only [h3333, h4696, hlam]
                                · rcases p4667_3 (m.d 0 3) (by simp) with h4698 | h4698
                                  · rcases p4667_3 (m.d 0 4) (by simp) with h4699 | h4699
                                    · linarith only [h4633, h4699, hlam]
                                    · linarith only [h4635, h4699, hlam]
                                  · linarith only [h4634, h4698, hlam]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              rcases p4667_3 (m.d 0 1) (by simp) with h4703 | h4703
                              · linarith only [h3104, h4703, hlam]
                              · rcases p4667_3 (m.d 0 2) (by simp) with h4705 | h4705
                                · linarith only [h4439, h4705, hlam]
                                · linarith only [h0, h4705, hlam]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              rcases p4667_3 (m.d 0 1) (by simp) with h4708 | h4708
                              · linarith only [h3104, h4708, hlam]
                              · rcases p4667_3 (m.d 0 2) (by simp) with h4710 | h4710
                                · linarith only [h4439, h4710, hlam]
                                · rcases p4667_3 (m.d 0 3) (by simp) with h4712 | h4712
                                  · rcases p4667_3 (m.d 0 4) (by simp) with h4713 | h4713
                                    · rcases p4667_3 (m.d 0 5) (by simp) with h4714 | h4714
                                      · linarith only [h4635, h4714, hlam]
                                      · linarith only [h4562, h4714, hlam]
                                    · linarith only [h4439, h4713, hlam]
                                  · linarith only [h3333, h4712, hlam]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h4633, hlam, p4667_0]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [hlam, p4667_0]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              rcases p4667_3 (m.d 0 1) (by simp) with h4721 | h4721
                              · linarith only [h3104, h4721, hlam]
                              · rcases p4667_3 (m.d 0 2) (by simp) with h4723 | h4723
                                · linarith only [h4439, h4723, hlam]
                                · rcases p4667_3 (m.d 0 3) (by simp) with h4725 | h4725
                                  · rcases p4667_3 (m.d 0 4) (by simp) with h4726 | h4726
                                    · rcases p4667_3 (m.d 0 5) (by simp) with h4727 | h4727
                                      · linarith only [h4635, h4727, hlam]
                                      · rcases h0emin with h4729 | h4729 | h4729 | h4729 | h4729
                                        · linarith only [h0, h4658, h4663, h4665, h4729, hc23, hlam, ht01, ht12]
                                        · linarith only [h0, h4658, h4663, h4665, h4729, hc23, hlam, ht01, ht12]
                                        · rcases h2bigk with h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h0, hlam, p4732_1]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h3333, hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h4439, hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h4562, hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h0, h4658, h4663, h4665, hc01, hc23, hlam, hphi, ht12, p4732_1]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h4636, hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h4656, hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h4658, hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            rcases p4732_3 (m.d 0 2) (by simp) with h4743 | h4743
                                            · linarith only [h4743, hlam, p4732_0]
                                            · rcases p4732_3 (m.d 1 2) (by simp) with h4745 | h4745
                                              · linarith only [h4636, h4745, hlam]
                                              · linarith only [h0, h4745, hlam]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4732_1]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h0, h4439, hc01, hc23, hlam, hphi, ht12, p4732_1]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h0, h4562, hc01, hc23, hlam, hphi, ht12, p4732_1]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            rcases p4732_3 (m.d 0 2) (by simp) with h4752 | h4752
                                            · linarith only [h4752, hlam, p4732_0]
                                            · rcases p4732_3 (m.d 1 2) (by simp) with h4754 | h4754
                                              · linarith only [h4656, h4754, hlam]
                                              · linarith only [h0, h4754, hlam]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4732_1]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h4663, hlam, p4732_1]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h3265, h4658, h4663, hc01, hc23, hlam, hphi, ht12, p4732_1]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            rcases p4732_3 (m.d 0 2) (by simp) with h4761 | h4761
                                            · linarith only [h4761, hlam, p4732_0]
                                            · rcases p4732_3 (m.d 1 2) (by simp) with h4763 | h4763
                                              · linarith only [h4658, h4763, hlam]
                                              · linarith only [h0, h4763, hlam]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4732_1]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h4664, hlam, p4732_1]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [h4665, hlam, p4732_0]
                                          · have p4732_0 := h4732c.1
                                            have p4732_1 := h4732c.2.1
                                            have p4732_2 := h4732c.2.2.1
                                            have p4732_3 := h4732c.2.2.2
                                            linarith only [hlam, p4732_0]
                                        · rcases h2bigk with h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c | h4770c
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h0, hlam, p4770_1]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h3333, hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h4439, hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h4562, hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h0, h4636, hc01, hc23, hlam, hphi, ht12, p4770_1]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h4636, hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h4656, hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h4658, hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            rcases p4770_3 (m.d 0 2) (by simp) with h4781 | h4781
                                            · linarith only [h4781, hlam, p4770_0]
                                            · rcases p4770_3 (m.d 1 2) (by simp) with h4783 | h4783
                                              · linarith only [h4636, h4783, hlam]
                                              · linarith only [h0, h4783, hlam]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4770_1]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h0, h4439, hc01, hc23, hlam, hphi, ht12, p4770_1]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h0, h4562, hc01, hc23, hlam, hphi, ht12, p4770_1]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            rcases p4770_3 (m.d 0 2) (by simp) with h4790 | h4790
                                            · linarith only [h4790, hlam, p4770_0]
                                            · rcases p4770_3 (m.d 1 2) (by simp) with h4792 | h4792
                                              · linarith only [h4656, h4792, hlam]
                                              · linarith only [h0, h4792, hlam]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4770_1]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h4663, hlam, p4770_1]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h0, h4658, h4663, hc01, hc23, hlam, hphi, ht12, p4770_1]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            rcases p4770_3 (m.d 0 2) (by simp) with h4799 | h4799
                                            · linarith only [h4799, hlam, p4770_0]
                                            · rcases p4770_3 (m.d 1 2) (by simp) with h4801 | h4801
                                              · linarith only [h4658, h4801, hlam]
                                              · linarith only [h0, h4801, hlam]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4770_1]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h4664, hlam, p4770_1]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [h4665, hlam, p4770_0]
                                          · have p4770_0 := h4770c.1
                                            have p4770_1 := h4770c.2.1
                                            have p4770_2 := h4770c.2.2.1
                                            have p4770_3 := h4770c.2.2.2
                                            linarith only [hlam, p4770_0]
                                        · linarith only [h4729, hc04, hlam, p4667_1]
                                    · linarith only [h4635, h4726, hlam]
                                  · linarith only [h4634, h4725, hlam]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              rcases p4667_3 (m.d 0 1) (by simp) with h4811 | h4811
                              · linarith only [h3265, h4811, hlam]
                              · rcases p4667_3 (m.d 0 2) (by simp) with h4813 | h4813
                                · linarith only [h4562, h4813, hlam]
                                · linarith only [h0, h4813, hlam]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              rcases p4667_3 (m.d 0 1) (by simp) with h4816 | h4816
                              · linarith only [h3265, h4816, hlam]
                              · rcases p4667_3 (m.d 0 2) (by simp) with h4818 | h4818
                                · linarith only [h4562, h4818, hlam]
                                · rcases p4667_3 (m.d 0 3) (by simp) with h4820 | h4820
                                  · rcases p4667_3 (m.d 0 4) (by simp) with h4821 | h4821
                                    · rcases p4667_3 (m.d 0 5) (by simp) with h4822 | h4822
                                      · rcases h0emin with h4823 | h4823 | h4823 | h4823 | h4823
                                        · linarith only [h0, h4823, hc12, hlam, ht01]
                                        · linarith only [h3333, h4823, hc23, hlam, ht01, ht12]
                                        · rcases h2bigk with h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c | h4826c
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h0, hlam, p4826_1]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h3333, hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h4439, hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h4562, hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h0, h4658, h4663, h4665, hc01, hc23, hlam, hphi, ht12, p4826_1]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h4636, hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h4656, hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h4658, hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            rcases p4826_3 (m.d 0 2) (by simp) with h4837 | h4837
                                            · linarith only [h4837, hlam, p4826_0]
                                            · rcases p4826_3 (m.d 1 2) (by simp) with h4839 | h4839
                                              · linarith only [h4636, h4839, hlam]
                                              · linarith only [h0, h4839, hlam]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4826_1]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h3104, h4656, hc01, hc23, hlam, hphi, ht12, p4826_1]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h0, h3265, h4658, hc01, hc23, hlam, hphi, ht12, p4667_1, p4826_1]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            rcases p4826_3 (m.d 0 2) (by simp) with h4846 | h4846
                                            · linarith only [h4846, hlam, p4826_0]
                                            · rcases p4826_3 (m.d 1 2) (by simp) with h4848 | h4848
                                              · linarith only [h4656, h4848, hlam]
                                              · linarith only [h0, h4848, hlam]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4826_1]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h4663, hlam, p4826_1]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h0, h3265, h4658, h4663, hc01, hc23, hlam, hphi, ht12, p4667_1, p4826_1]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            rcases p4826_3 (m.d 0 2) (by simp) with h4855 | h4855
                                            · linarith only [h4855, hlam, p4826_0]
                                            · rcases p4826_3 (m.d 1 2) (by simp) with h4857 | h4857
                                              · linarith only [h4658, h4857, hlam]
                                              · linarith only [h0, h4857, hlam]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4826_1]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h4664, hlam, p4826_1]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [h4665, hlam, p4826_0]
                                          · have p4826_0 := h4826c.1
                                            have p4826_1 := h4826c.2.1
                                            have p4826_2 := h4826c.2.2.1
                                            have p4826_3 := h4826c.2.2.2
                                            linarith only [hlam, p4826_0]
                                        · rcases h2bigk with h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h0, hlam, p4864_1]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h3333, hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h4439, hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h4562, hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h0, h4636, hc01, hc23, hlam, hphi, ht12, p4864_1]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h4636, hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h4656, hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h4658, hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            rcases p4864_3 (m.d 0 2) (by simp) with h4875 | h4875
                                            · linarith only [h4875, hlam, p4864_0]
                                            · rcases p4864_3 (m.d 1 2) (by simp) with h4877 | h4877
                                              · linarith only [h4636, h4877, hlam]
                                              · linarith only [h0, h4877, hlam]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4864_1]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h0, h4439, hc01, hc23, hlam, hphi, ht12, p4864_1]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h0, h4562, hc01, hc23, hlam, hphi, ht12, p4864_1]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            rcases p4864_3 (m.d 0 2) (by simp) with h4884 | h4884
                                            · linarith only [h4884, hlam, p4864_0]
                                            · rcases p4864_3 (m.d 1 2) (by simp) with h4886 | h4886
                                              · linarith only [h4656, h4886, hlam]
                                              · linarith only [h0, h4886, hlam]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4864_1]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h4663, hlam, p4864_1]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h0, h3265, h4658, h4663, hc01, hc23, hlam, hphi, ht12, p4667_1, p4864_1]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            rcases p4864_3 (m.d 0 2) (by simp) with h4893 | h4893
                                            · linarith only [h4893, hlam, p4864_0]
                                            · rcases p4864_3 (m.d 1 2) (by simp) with h4895 | h4895
                                              · linarith only [h4658, h4895, hlam]
                                              · linarith only [h0, h4895, hlam]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4864_1]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h4664, hlam, p4864_1]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [h4665, hlam, p4864_0]
                                          · have p4864_0 := h4864c.1
                                            have p4864_1 := h4864c.2.1
                                            have p4864_2 := h4864c.2.2.1
                                            have p4864_3 := h4864c.2.2.2
                                            linarith only [hlam, p4864_0]
                                        · rcases h2bigk with h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h0, hlam, p4902_1]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h3333, hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h4439, hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h4562, hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h0, h4636, hc01, hc23, hlam, hphi, ht12, p4902_1]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h4636, hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h4656, hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h4658, hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            rcases p4902_3 (m.d 0 2) (by simp) with h4913 | h4913
                                            · linarith only [h4913, hlam, p4902_0]
                                            · rcases p4902_3 (m.d 1 2) (by simp) with h4915 | h4915
                                              · linarith only [h4636, h4915, hlam]
                                              · linarith only [h0, h4915, hlam]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4902_1]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h0, h4439, hc01, hc23, hlam, hphi, ht12, p4902_1]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h0, h4562, hc01, hc23, hlam, hphi, ht12, p4902_1]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            rcases p4902_3 (m.d 0 2) (by simp) with h4922 | h4922
                                            · linarith only [h4922, hlam, p4902_0]
                                            · rcases p4902_3 (m.d 1 2) (by simp) with h4924 | h4924
                                              · linarith only [h4656, h4924, hlam]
                                              · linarith only [h0, h4924, hlam]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4902_1]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h4663, hlam, p4902_1]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h0, h3265, h4658, h4663, hc01, hc23, hlam, hphi, ht12, p4667_1, p4902_1]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            rcases p4902_3 (m.d 0 2) (by simp) with h4931 | h4931
                                            · linarith only [h4931, hlam, p4902_0]
                                            · rcases p4902_3 (m.d 1 2) (by simp) with h4933 | h4933
                                              · linarith only [h4658, h4933, hlam]
                                              · linarith only [h0, h4933, hlam]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4902_1]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h4664, hlam, p4902_1]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [h4665, hlam, p4902_0]
                                          · have p4902_0 := h4902c.1
                                            have p4902_1 := h4902c.2.1
                                            have p4902_2 := h4902c.2.2.1
                                            have p4902_3 := h4902c.2.2.2
                                            linarith only [hlam, p4902_0]
                                      · linarith only [h4562, h4822, hlam]
                                    · linarith only [h4439, h4821, hlam]
                                  · linarith only [h3333, h4820, hlam]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h4634, hlam, p4667_0]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [h4635, hlam, p4667_1]
                            · have p4667_0 := h4667c.1
                              have p4667_1 := h4667c.2.1
                              have p4667_2 := h4667c.2.2.1
                              have p4667_3 := h4667c.2.2.2
                              linarith only [hlam, p4667_0]
                          · rcases h0bigk with h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c | h4946c
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [hlam, p4946_0]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h0, hlam, p4946_1]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h2914, hlam, p4946_0]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h3104, hlam, p4946_1]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h3265, hlam, p4946_1]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h3333, hc01, hc23, hlam, hphi, ht12, p4946_1]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [hlam, p4946_0]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h3333, hlam, p4946_0]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h4439, hlam, p4946_1]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h4562, hlam, p4946_0]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              rcases p4946_3 (m.d 0 1) (by simp) with h4957 | h4957
                              · linarith only [h2914, h4957, hlam]
                              · rcases p4946_3 (m.d 0 2) (by simp) with h4959 | h4959
                                · linarith only [h3333, h4959, hlam]
                                · linarith only [h0, h4959, hlam]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              rcases p4946_3 (m.d 0 1) (by simp) with h4962 | h4962
                              · linarith only [h2914, h4962, hlam]
                              · rcases p4946_3 (m.d 0 2) (by simp) with h4964 | h4964
                                · linarith only [h3333, h4964, hlam]
                                · rcases p4946_3 (m.d 0 3) (by simp) with h4966 | h4966
                                  · rcases p4946_3 (m.d 0 4) (by simp) with h4967 | h4967
                                    · linarith only [h4633, h4967, hlam]
                                    · linarith only [h4439, h4967, hlam]
                                  · linarith only [h3333, h4966, hlam]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [hlam, p4946_0]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h2914, h4635, h4636, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4946_1, u5ehi4]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h2914, h4635, h4636, h4666, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4946_1, u3ehi3]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              rcases p4946_3 (m.d 0 1) (by simp) with h4974 | h4974
                              · linarith only [h3104, h4974, hlam]
                              · rcases p4946_3 (m.d 0 2) (by simp) with h4976 | h4976
                                · linarith only [h4439, h4976, hlam]
                                · linarith only [h0, h4976, hlam]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              rcases p4946_3 (m.d 0 1) (by simp) with h4979 | h4979
                              · linarith only [h3104, h4979, hlam]
                              · rcases p4946_3 (m.d 0 2) (by simp) with h4981 | h4981
                                · linarith only [h4439, h4981, hlam]
                                · rcases p4946_3 (m.d 0 3) (by simp) with h4983 | h4983
                                  · rcases p4946_3 (m.d 0 4) (by simp) with h4984 | h4984
                                    · rcases p4946_3 (m.d 0 5) (by simp) with h4985 | h4985
                                      · linarith only [h4635, h4985, hlam]
                                      · linarith only [h4562, h4985, hlam]
                                    · linarith only [h4439, h4984, hlam]
                                  · linarith only [h3333, h4983, hlam]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h4633, hlam, p4946_0]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [hlam, p4946_0]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h4635, h4666, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p4946_1, u3ehi3]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              rcases p4946_3 (m.d 0 1) (by simp) with h4993 | h4993
                              · linarith only [h3265, h4993, hlam]
                              · rcases p4946_3 (m.d 0 2) (by simp) with h4995 | h4995
                                · linarith only [h4562, h4995, hlam]
                                · linarith only [h0, h4995, hlam]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              rcases p4946_3 (m.d 0 1) (by simp) with h4998 | h4998
                              · linarith only [h3265, h4998, hlam]
                              · rcases p4946_3 (m.d 0 2) (by simp) with h5000 | h5000
                                · linarith only [h4562, h5000, hlam]
                                · rcases p4946_3 (m.d 0 3) (by simp) with h5002 | h5002
                                  · rcases p4946_3 (m.d 0 4) (by simp) with h5003 | h5003
                                    · rcases p4946_3 (m.d 0 5) (by simp) with h5004 | h5004
                                      · rcases h0emin with h5005 | h5005 | h5005 | h5005 | h5005
                                        · linarith only [h0, h5005, hc05, hlam, p4946_1]
                                        · linarith only [h5005, hc05, hlam, p4946_1]
                                        · rcases h2bigk with h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c | h5008c
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h0, hlam, p5008_1]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h3333, hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h4439, hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h4562, hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h0, h4658, h4663, h4665, hc01, hc23, hlam, hphi, ht12, p5008_1]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h4636, hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h4656, hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h4658, hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            rcases p5008_3 (m.d 0 2) (by simp) with h5019 | h5019
                                            · linarith only [h5019, hlam, p5008_0]
                                            · rcases p5008_3 (m.d 1 2) (by simp) with h5021 | h5021
                                              · linarith only [h4636, h5021, hlam]
                                              · linarith only [h0, h5021, hlam]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p5008_1]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h3104, h4656, hc01, hc23, hlam, hphi, ht12, p5008_1]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h0, h3265, h4658, hc01, hc23, hlam, hphi, ht12, p4946_1, p5008_1]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            rcases p5008_3 (m.d 0 2) (by simp) with h5028 | h5028
                                            · linarith only [h5028, hlam, p5008_0]
                                            · rcases p5008_3 (m.d 1 2) (by simp) with h5030 | h5030
                                              · linarith only [h4656, h5030, hlam]
                                              · linarith only [h0, h5030, hlam]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p5008_1]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h4663, hlam, p5008_1]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h0, h3265, h4658, h4663, hc01, hc23, hlam, hphi, ht12, p4946_1, p5008_1]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            rcases p5008_3 (m.d 0 2) (by simp) with h5037 | h5037
                                            · linarith only [h5037, hlam, p5008_0]
                                            · rcases p5008_3 (m.d 1 2) (by simp) with h5039 | h5039
                                              · linarith only [h4658, h5039, hlam]
                                              · linarith only [h0, h5039, hlam]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p5008_1]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h4664, hlam, p5008_1]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [h4665, hlam, p5008_0]
                                          · have p5008_0 := h5008c.1
                                            have p5008_1 := h5008c.2.1
                                            have p5008_2 := h5008c.2.2.1
                                            have p5008_3 := h5008c.2.2.2
                                            linarith only [hlam, p5008_0]
                                        · rcases h2bigk with h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h0, hlam, p5046_1]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h3333, hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h4439, hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h4562, hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h0, h4636, hc01, hc23, hlam, hphi, ht12, p5046_1]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h4636, hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h4656, hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h4658, hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            rcases p5046_3 (m.d 0 2) (by simp) with h5057 | h5057
                                            · linarith only [h5057, hlam, p5046_0]
                                            · rcases p5046_3 (m.d 1 2) (by simp) with h5059 | h5059
                                              · linarith only [h4636, h5059, hlam]
                                              · linarith only [h0, h5059, hlam]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p5046_1]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h0, h4439, hc01, hc23, hlam, hphi, ht12, p5046_1]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h0, h4562, hc01, hc23, hlam, hphi, ht12, p5046_1]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            rcases p5046_3 (m.d 0 2) (by simp) with h5066 | h5066
                                            · linarith only [h5066, hlam, p5046_0]
                                            · rcases p5046_3 (m.d 1 2) (by simp) with h5068 | h5068
                                              · linarith only [h4656, h5068, hlam]
                                              · linarith only [h0, h5068, hlam]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p5046_1]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h4663, hlam, p5046_1]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h0, h3265, h4658, h4663, hc01, hc23, hlam, hphi, ht12, p4946_1, p5046_1]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            rcases p5046_3 (m.d 0 2) (by simp) with h5075 | h5075
                                            · linarith only [h5075, hlam, p5046_0]
                                            · rcases p5046_3 (m.d 1 2) (by simp) with h5077 | h5077
                                              · linarith only [h4658, h5077, hlam]
                                              · linarith only [h0, h5077, hlam]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p5046_1]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h4664, hlam, p5046_1]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [h4665, hlam, p5046_0]
                                          · have p5046_0 := h5046c.1
                                            have p5046_1 := h5046c.2.1
                                            have p5046_2 := h5046c.2.2.1
                                            have p5046_3 := h5046c.2.2.2
                                            linarith only [hlam, p5046_0]
                                        · rcases h2bigk with h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c | h5084c
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h0, hlam, p5084_1]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h3333, hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h4439, hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h4562, hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h0, h4636, hc01, hc23, hlam, hphi, ht12, p5084_1]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h4636, hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h4656, hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h4658, hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            rcases p5084_3 (m.d 0 2) (by simp) with h5095 | h5095
                                            · linarith only [h5095, hlam, p5084_0]
                                            · rcases p5084_3 (m.d 1 2) (by simp) with h5097 | h5097
                                              · linarith only [h4636, h5097, hlam]
                                              · linarith only [h0, h5097, hlam]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p5084_1]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h0, h4439, hc01, hc23, hlam, hphi, ht12, p5084_1]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h0, h4562, hc01, hc23, hlam, hphi, ht12, p5084_1]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            rcases p5084_3 (m.d 0 2) (by simp) with h5104 | h5104
                                            · linarith only [h5104, hlam, p5084_0]
                                            · rcases p5084_3 (m.d 1 2) (by simp) with h5106 | h5106
                                              · linarith only [h4656, h5106, hlam]
                                              · linarith only [h0, h5106, hlam]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p5084_1]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h4663, hlam, p5084_1]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h0, h3265, h4658, h4663, hc01, hc23, hlam, hphi, ht12, p4946_1, p5084_1]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            rcases p5084_3 (m.d 0 2) (by simp) with h5113 | h5113
                                            · linarith only [h5113, hlam, p5084_0]
                                            · rcases p5084_3 (m.d 1 2) (by simp) with h5115 | h5115
                                              · linarith only [h4658, h5115, hlam]
                                              · linarith only [h0, h5115, hlam]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p5084_1]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h4664, hlam, p5084_1]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [h4665, hlam, p5084_0]
                                          · have p5084_0 := h5084c.1
                                            have p5084_1 := h5084c.2.1
                                            have p5084_2 := h5084c.2.2.1
                                            have p5084_3 := h5084c.2.2.2
                                            linarith only [hlam, p5084_0]
                                      · linarith only [h4562, h5004, hlam]
                                    · linarith only [h4439, h5003, hlam]
                                  · linarith only [h3333, h5002, hlam]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h4634, hlam, p4946_0]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [h4635, hlam, p4946_1]
                            · have p4946_0 := h4946c.1
                              have p4946_1 := h4946c.2.1
                              have p4946_2 := h4946c.2.2.1
                              have p4946_3 := h4946c.2.2.2
                              linarith only [hlam, p4946_0]
                        · linarith only [h0, h3104, h4439, h4635, h4665, hc01, hc14, hlam, hphi]
                      · linarith only [h2914, h4633, h4636, h4664, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h0, h4633, h4636, h4663, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h2914, h3104, h4633, h4635, h4636, h4662, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h2914, h4634, h4661, hlam]
              · linarith only [h2914, h4633, h4660, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5134 | h5134
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5135 | h5135
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5136 | h5136
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5137 | h5137
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5138 | h5138
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5139 | h5139
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5140 | h5140
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5141 | h5141
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5142 | h5142
                        · linarith only [h4633, h4635, h5135, h5142, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h4439, h5134, h5137, h5139, h5142, hc01, hc12, hlam, hphi]
                      · linarith only [h3333, h4633, h5141, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3333, h4634, h5140, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5147 | h5147
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5148 | h5148
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5149 | h5149
                        · linarith only [h3104, h5139, h5149, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5151 | h5151
                          · linarith only [h0, h4439, h4633, h5135, h5139, h5151, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases h0bigk with h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h0, hlam, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h2914, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3104, hlam, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3265, hlam, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h4439, h5135, hc01, hc14, hlam, hphi, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3333, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h4439, hlam, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h4562, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3333, h5134, hc01, hc12, hlam, hphi, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h0, h3333, h5134, hc01, hc12, hlam, hphi, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3104, h3333, h5134, hc01, hc12, hlam, hphi, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3333, h5134, hc12, hlam, hphi, ht01, ht0b, ht5b, p5153_1, u5ehi0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3104, h3333, h4634, h5134, h5139, h5151, hc01, hc12, hc45, hlam, hphi, ht34, p5153_1, u3ehi3]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h0, h3333, h4439, h4634, h5134, h5135, h5139, h5151, hc01, hc12, hc45, hlam, hphi, ht34, p5153_1, u3ehi3]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h4633, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h4635, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3333, h4634, h5134, hc01, hc12, hlam, hphi, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h0, h3333, h4634, h5134, hc01, hc12, hlam, hphi, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h4634, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3104, h3333, h4634, h5134, hc01, hc12, hlam, hphi, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [hlam, p5153_0]
                      · linarith only [h3333, h4634, h5148, hlam]
                    · linarith only [h3333, h4634, h5147, hc34, hlam, hphi, u3ehi4]
                · linarith only [h3333, h4634, h5134, h5138, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h3333, h4633, h5134, h5137, hlam]
            · linarith only [h3333, h4634, h5134, h5136, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · linarith only [h3333, h4633, h5134, h5135, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5185 | h5185
          · linarith only [h0, h4439, h5134, h5185, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5187 | h5187
            · linarith only [h0, h4562, h5185, h5187, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5189 | h5189
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5190 | h5190
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5191 | h5191
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5192 | h5192
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5193 | h5193
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5194 | h5194
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5195 | h5195
                          · linarith only [h2914, h3104, h4633, h4635, h5134, h5195, hc01, hc23, hlam, hphi, ht12]
                          · rcases h0bigk with h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c | h5197c
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [hlam, p5197_0]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h0, hlam, p5197_1]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h2914, hlam, p5197_0]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h3104, hlam, p5197_1]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h3265, hlam, p5197_1]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h0, h5187, h5192, h5194, hc01, hc23, hlam, hphi, ht12, p5197_1]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [hlam, p5197_0]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h3333, hlam, p5197_0]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h4439, hlam, p5197_1]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h4562, hlam, p5197_0]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              rcases p5197_3 (m.d 0 1) (by simp) with h5208 | h5208
                              · linarith only [h2914, h5208, hlam]
                              · rcases p5197_3 (m.d 0 2) (by simp) with h5210 | h5210
                                · linarith only [h3333, h5210, hlam]
                                · linarith only [h0, h5210, hlam]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              rcases p5197_3 (m.d 0 1) (by simp) with h5213 | h5213
                              · linarith only [h2914, h5213, hlam]
                              · rcases p5197_3 (m.d 0 2) (by simp) with h5215 | h5215
                                · linarith only [h3333, h5215, hlam]
                                · rcases p5197_3 (m.d 0 3) (by simp) with h5217 | h5217
                                  · rcases p5197_3 (m.d 0 4) (by simp) with h5218 | h5218
                                    · linarith only [h4633, h5218, hlam]
                                    · linarith only [h4439, h5218, hlam]
                                  · linarith only [h3333, h5217, hlam]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [hlam, p5197_0]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              rcases p5197_3 (m.d 0 1) (by simp) with h5223 | h5223
                              · linarith only [h2914, h5223, hlam]
                              · rcases p5197_3 (m.d 0 2) (by simp) with h5225 | h5225
                                · linarith only [h3333, h5225, hlam]
                                · rcases p5197_3 (m.d 0 3) (by simp) with h5227 | h5227
                                  · rcases p5197_3 (m.d 0 4) (by simp) with h5228 | h5228
                                    · linarith only [h4633, h5228, hlam]
                                    · rcases p5197_3 (m.d 0 5) (by simp) with h5230 | h5230
                                      · linarith only [h4634, h5230, hlam]
                                      · linarith only [h4635, h5230, hlam]
                                  · linarith only [h4633, h5227, hlam]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              rcases p5197_3 (m.d 0 1) (by simp) with h5234 | h5234
                              · linarith only [h2914, h5234, hlam]
                              · rcases p5197_3 (m.d 0 2) (by simp) with h5236 | h5236
                                · linarith only [h3333, h5236, hlam]
                                · rcases p5197_3 (m.d 0 3) (by simp) with h5238 | h5238
                                  · rcases p5197_3 (m.d 0 4) (by simp) with h5239 | h5239
                                    · linarith only [h4633, h5239, hlam]
                                    · rcases p5197_3 (m.d 0 5) (by simp) with h5241 | h5241
                                      · linarith only [h4634, h5241, hlam]
                                      · rcases h0emin with h5243 | h5243 | h5243 | h5243 | h5243
                                        · linarith only [h0, h5187, h5192, h5194, h5243, hc23, hlam, ht01, ht12]
                                        · linarith only [h4439, h4635, h5191, h5243, hc14, hlam, ht01]
                                        · rcases h2bigk with h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c | h5246c
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h0, hlam, p5246_1]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h3333, hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h4439, hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h4562, hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h0, h5187, h5192, h5194, hc01, hc23, hlam, hphi, ht12, p5246_1]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h5134, hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h5185, hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h5187, hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            rcases p5246_3 (m.d 0 2) (by simp) with h5257 | h5257
                                            · linarith only [h5257, hlam, p5246_0]
                                            · rcases p5246_3 (m.d 1 2) (by simp) with h5259 | h5259
                                              · linarith only [h5134, h5259, hlam]
                                              · linarith only [h0, h5259, hlam]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p5246_1]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h5185, h5191, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5246_1, u5ehi4]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h0, h4562, hc01, hc23, hlam, hphi, ht12, p5246_1]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            rcases p5246_3 (m.d 0 2) (by simp) with h5266 | h5266
                                            · linarith only [h5266, hlam, p5246_0]
                                            · rcases p5246_3 (m.d 1 2) (by simp) with h5268 | h5268
                                              · linarith only [h5185, h5268, hlam]
                                              · linarith only [h0, h5268, hlam]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p5246_1]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h5192, hlam, p5246_1]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h0, h5187, h5192, hc01, hc23, hlam, hphi, ht12, p5246_1]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            rcases p5246_3 (m.d 0 2) (by simp) with h5275 | h5275
                                            · linarith only [h5275, hlam, p5246_0]
                                            · rcases p5246_3 (m.d 1 2) (by simp) with h5277 | h5277
                                              · linarith only [h5187, h5277, hlam]
                                              · linarith only [h0, h5277, hlam]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p5246_1]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h5193, hlam, p5246_1]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [h5194, hlam, p5246_0]
                                          · have p5246_0 := h5246c.1
                                            have p5246_1 := h5246c.2.1
                                            have p5246_2 := h5246c.2.2.1
                                            have p5246_3 := h5246c.2.2.2
                                            linarith only [hlam, p5246_0]
                                        · linarith only [h4635, h5191, h5243, hc14, hlam, ht01]
                                        · linarith only [h2914, h5134, h5243, hc23, hlam, ht01, ht12, p5197_1]
                                  · linarith only [h4634, h5238, hlam]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h4635, h5191, hc01, hc14, hlam, hphi, p5197_1]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h0, h4635, h5191, hc01, hc14, hlam, hphi, p5197_1]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h4633, hlam, p5197_0]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [hlam, p5197_0]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h4635, hlam, p5197_0]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h4635, h5191, hc01, hc14, hlam, hphi, p5197_1]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h0, h4635, h5191, hc01, hc14, hlam, hphi, p5197_1]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h4634, hlam, p5197_0]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [h3104, h4635, h5191, hc01, hc14, hlam, hphi, p5197_1]
                            · have p5197_0 := h5197c.1
                              have p5197_1 := h5197c.2.1
                              have p5197_2 := h5197c.2.2.1
                              have p5197_3 := h5197c.2.2.2
                              linarith only [hlam, p5197_0]
                        · linarith only [h5185, h5191, h5194, hlam]
                      · linarith only [h2914, h4633, h5134, h5193, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h4633, h4635, h5134, h5189, h5191, h5192, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5300 | h5300
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5301 | h5301
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5302 | h5302
                        · linarith only [h3104, h5191, h5302, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h5185, h5302, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h2914, h4633, h5134, h5301, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h2914, h4633, h5134, h5300, hlam]
                · linarith only [h2914, h4634, h5190, hlam]
              · linarith only [h2914, h4633, h5189, hlam]
    · linarith only [h4633, h4634, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h5310 | h5310
    · linarith only [h4633, h5310, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h5312 | h5312
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5313 | h5313
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5314 | h5314
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5315 | h5315
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5316 | h5316
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5317 | h5317
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5318 | h5318
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5319 | h5319
                    · linarith only [h4633, h5313, h5319, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h0, h3333, h5316, h5319, hc01, hc13, hlam, hphi]
                  · linarith only [h3104, h4439, h5312, h5318, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h4633, h5316, h5317, hc35, hlam, hphi, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5324 | h5324
                · linarith only [h5316, h5324, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5326 | h5326
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5327 | h5327
                    · linarith only [h2914, h5316, h5327, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5329 | h5329
                      · linarith only [h5313, h5324, h5329, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5331 | h5331
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5332 | h5332
                          · rcases h0bigk with h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [hlam, p5333_0]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h0, hlam, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h2914, hlam, p5333_0]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h3104, hlam, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h3265, hlam, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h3333, h5313, hc01, hc13, hlam, hphi, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [hlam, p5333_0]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h3333, hlam, p5333_0]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h4439, hlam, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h4562, hlam, p5333_0]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h2914, h5324, h5332, hc01, hc34, hlam, hphi, ht12, ht23, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h2914, h5324, h5332, hc02, hc34, hlam, hphi, ht23, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [hlam, p5333_0]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h4633, hlam, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h5310, hlam, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h4439, h5314, hc01, hc12, hlam, hphi, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h0, h4439, h5314, hc01, hc12, hlam, hphi, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h4633, hc34, hlam, hphi, p5333_1, u3ehi0]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [hlam, p5333_0]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h4633, h5310, hc34, hlam, hphi, p5333_1, u3ehi0]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h4439, h5312, h5314, hc01, hc12, hlam, hphi, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h0, h4439, h5312, h5314, hc01, hc12, hlam, hphi, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h5310, hc35, hlam, hphi, p5333_1, u3ehi0]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [h5312, hlam, p5333_1]
                            · have p5333_0 := h5333c.1
                              have p5333_1 := h5333c.2.1
                              have p5333_2 := h5333c.2.2.1
                              have p5333_3 := h5333c.2.2.2
                              linarith only [hlam, p5333_0]
                          · linarith only [h4633, h5332, hc45, hlam, hphi, ht34, u3ehi0]
                        · linarith only [h0, h3104, h4439, h5312, h5331, hc01, hc14, hlam, hphi]
                  · linarith only [h4439, h5312, h5314, h5326, hlam]
            · linarith only [h4439, h5312, h5314, h5315, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · linarith only [h0, h3333, h5313, h5314, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5364 | h5364
          · linarith only [h0, h4439, h5313, h5364, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5366 | h5366
            · linarith only [h0, h4562, h5313, h5366, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5368 | h5368
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5369 | h5369
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5370 | h5370
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5371 | h5371
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5372 | h5372
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5373 | h5373
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5374 | h5374
                          · rcases h0bigk with h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c | h5375c
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [hlam, p5375_0]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h0, hlam, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h2914, hlam, p5375_0]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h3104, hlam, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h3265, hlam, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h0, h5366, h5371, h5373, hc01, hc23, hlam, hphi, ht12, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [hlam, p5375_0]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h3333, hlam, p5375_0]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h4439, hlam, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h4562, hlam, p5375_0]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h5310, h5368, h5374, hc01, hc13, hlam, hphi, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h5310, h5368, h5374, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [hlam, p5375_0]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h4633, hlam, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h5310, hlam, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h4633, h5368, hc01, hc13, hlam, hphi, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h0, h4633, h5368, hc01, hc13, hlam, hphi, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h4633, h5368, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5375_1, u3ehi0]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [hlam, p5375_0]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h4633, h5310, h5368, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5375_1, u3ehi0]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h5310, h5368, h5374, hc01, hc13, hlam, hphi, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h0, h5310, h5368, h5374, hc01, hc13, hlam, hphi, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h5310, h5368, h5374, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5375_1, u3ehi0]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [h5312, hlam, p5375_1]
                            · have p5375_0 := h5375c.1
                              have p5375_1 := h5375c.2.1
                              have p5375_2 := h5375c.2.2.1
                              have p5375_3 := h5375c.2.2.2
                              linarith only [hlam, p5375_0]
                          · linarith only [h4633, h5374, hc45, hlam, hphi, ht34, u3ehi0]
                        · linarith only [h0, h4439, h4633, h5312, h5368, h5373, hc01, hc13, hlam, hphi]
                      · linarith only [h4633, h5312, h5313, h5368, h5372, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · linarith only [h5313, h5368, h5371, hlam]
                  · linarith only [h4633, h5312, h5368, h5370, hlam]
                · linarith only [h4633, h5312, h5368, h5369, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5407 | h5407
                · linarith only [h5368, h5407, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5409 | h5409
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5410 | h5410
                    · linarith only [h2914, h5368, h5410, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h5313, h5410, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3104, h5312, h5409, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5414 | h5414
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5415 | h5415
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5416 | h5416
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5417 | h5417
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5418 | h5418
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5419 | h5419
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5420 | h5420
                    · linarith only [h4633, h5414, h5420, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h0, h3333, h5414, h5417, h5420, hc01, hc12, hlam, hphi]
                  · linarith only [h4633, h5417, h5419, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h4633, h5417, h5418, hc35, hlam, hphi, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5425 | h5425
                · linarith only [h5417, h5425, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5427 | h5427
                  · linarith only [h4633, h5312, h5417, h5427, hc34, hlam, hphi, u3ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5429 | h5429
                    · linarith only [h5414, h5417, h5427, h5429, hc45, hlam, hphi, ht34, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5431 | h5431
                      · linarith only [h5414, h5417, h5427, h5431, hc45, hlam, hphi, ht34, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5433 | h5433
                        · linarith only [h3333, h5414, h5417, h5427, h5433, hc02, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5435 | h5435
                          · linarith only [h0, h3333, h5414, h5417, h5427, h5435, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h4633, h5435, hc45, hlam, hphi, ht34, u3ehi0]
            · linarith only [h0, h3333, h5414, h5416, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h3333, h5414, h5415, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5440 | h5440
          · linarith only [h0, h4439, h5414, h5440, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5442 | h5442
            · linarith only [h0, h4562, h5414, h5442, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5444 | h5444
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5445 | h5445
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5446 | h5446
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5447 | h5447
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5448 | h5448
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5449 | h5449
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5450 | h5450
                          · linarith only [h4633, h5312, h5450, hc34, hlam, hphi, u3ehi0]
                          · linarith only [h4633, h5414, h5444, h5446, h5450, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h4439, h5414, h5444, h5446, h5449, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h3104, h5312, h5414, h5444, h5446, h5448, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h4633, h5312, h5414, h5444, h5446, h5447, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h4633, h5444, h5446, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h4633, h5444, h5445, hc35, hlam, hphi, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5458 | h5458
                · linarith only [h5444, h5458, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5460 | h5460
                  · linarith only [h4633, h5312, h5444, h5460, hc34, hlam, hphi, u3ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5462 | h5462
                    · linarith only [h0, h5414, h5444, h5462, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h5414, h5462, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
