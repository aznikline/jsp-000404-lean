import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16170000 in
set_option maxHeartbeats 16170000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s10_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h7600 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h7601 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h7602 | h7602
  · rcases m.htr 0 2 3 (by decide) (by decide) with h7603 | h7603
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7604 | h7604
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7605 | h7605
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7606 | h7606
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7607 | h7607
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7608 | h7608
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7609 | h7609
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7610 | h7610
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7611 | h7611
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7612 | h7612
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7613 | h7613
                        · linarith only [h0, h7600, h7613, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h7600, h7607, h7612, h7613, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7616 | h7616
                        · linarith only [h0, h7600, h7616, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7618 | h7618
                          · linarith only [h0, h7600, h7606, h7612, h7618, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7620 | h7620
                            · linarith only [h0, h7601, h7608, h7609, h7612, h7618, h7620, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7622 | h7622
                              · linarith only [h7609, h7616, h7622, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7624 | h7624
                                · linarith only [h7610, h7618, h7624, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7626 | h7626
                                  · linarith only [h0, h7600, h7606, h7618, h7626, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h7600, h7606, h7608, h7609, h7612, h7626, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h7600, h7606, h7608, h7611, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h7600, h7606, h7608, h7610, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h7600, h7606, h7608, h7609, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7632 | h7632
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7633 | h7633
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7634 | h7634
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7635 | h7635
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7636 | h7636
                        · linarith only [h0, h7600, h7636, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h7600, h7607, h7635, h7636, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7639 | h7639
                        · linarith only [h0, h7600, h7639, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7641 | h7641
                          · linarith only [h0, h7600, h7606, h7608, h7635, h7641, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7643 | h7643
                            · linarith only [h7632, h7635, h7643, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7645 | h7645
                              · linarith only [h0, h7600, h7632, h7634, h7639, h7645, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7647 | h7647
                                · linarith only [h7604, h7608, h7647, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7649 | h7649
                                  · linarith only [h7606, h7608, h7649, hlam]
                                  · rcases h0bigk with h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [hlam, p7651_0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h0, hlam, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h7607, h7632, h7635, h7649, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h0, h7606, h7632, h7635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p7651_1, u5ehi0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h0, h7600, h7607, h7632, h7635, h7649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [hlam, p7651_0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h0, h7607, h7632, h7635, h7649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      rcases p7651_3 (m.d 0 1) (by simp) with h7660 | h7660
                                      · linarith only [h0, h7660, hlam]
                                      · linarith only [h7601, h7660, hlam]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      rcases p7651_3 (m.d 0 1) (by simp) with h7663 | h7663
                                      · linarith only [h0, h7663, hlam]
                                      · linarith only [h7602, h7663, hlam]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h7600, hlam, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h7603, hlam, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [hlam, p7651_0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h0, h7600, h7606, h7632, h7635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h0, h7600, h7607, h7632, h7635, h7649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h7601, hlam, p7651_0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h7604, hlam, p7651_0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h7606, hlam, p7651_0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [hlam, p7651_0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h7608, hlam, p7651_0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h7602, hlam, p7651_0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h7605, hlam, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h7607, hlam, p7651_0]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [h0, h7602, h7606, h7632, h7635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7651_1]
                                    · have p7651_0 := h7651c.1
                                      have p7651_1 := h7651c.2.1
                                      have p7651_2 := h7651c.2.2.1
                                      have p7651_3 := h7651c.2.2.2
                                      linarith only [hlam, p7651_0]
                    · linarith only [h0, h7602, h7634, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h7600, h7607, h7633, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h0, h7600, h7607, h7632, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7684 | h7684
              · linarith only [h7606, h7607, h7684, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7686 | h7686
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7687 | h7687
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7688 | h7688
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7689 | h7689
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7690 | h7690
                        · linarith only [h7600, h7607, h7690, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7692 | h7692
                          · linarith only [h7601, h7684, h7692, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7694 | h7694
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7695 | h7695
                              · linarith only [h7600, h7607, h7686, h7695, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7697 | h7697
                                · linarith only [h7601, h7684, h7687, h7697, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7699 | h7699
                                  · linarith only [h7600, h7601, h7607, h7684, h7686, h7687, h7694, h7699, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                  · rcases h0bigk with h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c | h7701c
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [hlam, p7701_0]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h0, hlam, p7701_1]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h0, h7606, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7701_1]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      rcases p7701_3 (m.d 0 1) (by simp) with h7705 | h7705
                                      · rcases p7701_3 (m.d 0 2) (by simp) with h7706 | h7706
                                        · rcases p7701_3 (m.d 0 3) (by simp) with h7707 | h7707
                                          · linarith only [h7600, h7707, hlam]
                                          · linarith only [h7606, h7707, hlam]
                                        · linarith only [h7604, h7706, hlam]
                                      · linarith only [h7601, h7705, hlam]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p7701_1, u5ehi0]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h0, h7600, h7686, h7694, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7701_1]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [hlam, p7701_0]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      rcases p7701_3 (m.d 0 1) (by simp) with h7715 | h7715
                                      · linarith only [h0, h7715, hlam]
                                      · linarith only [h7600, h7715, hlam]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      rcases p7701_3 (m.d 0 1) (by simp) with h7718 | h7718
                                      · linarith only [h0, h7718, hlam]
                                      · linarith only [h7601, h7718, hlam]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      rcases p7701_3 (m.d 0 1) (by simp) with h7721 | h7721
                                      · linarith only [h0, h7721, hlam]
                                      · linarith only [h7602, h7721, hlam]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h7600, hlam, p7701_1]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h7603, hlam, p7701_1]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [hlam, p7701_0]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h7601, h7607, h7687, h7694, h7699, hc34, hc45, hlam, hphi, p7701_1]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h7607, hlam, p7701_1]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h7601, hlam, p7701_0]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h7604, hlam, p7701_0]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h7606, hlam, p7701_0]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [hlam, p7701_0]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h7684, hlam, p7701_0]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h7602, hlam, p7701_0]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h7605, hlam, p7701_1]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [h0, h7600, h7602, h7686, h7694, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7701_1]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      rcases p7701_3 (m.d 0 1) (by simp) with h7737 | h7737
                                      · rcases p7701_3 (m.d 0 2) (by simp) with h7738 | h7738
                                        · rcases p7701_3 (m.d 0 3) (by simp) with h7739 | h7739
                                          · linarith only [h7607, h7739, hlam]
                                          · linarith only [h7606, h7739, hlam]
                                        · linarith only [h7604, h7738, hlam]
                                      · linarith only [h7601, h7737, hlam]
                                    · have p7701_0 := h7701c.1
                                      have p7701_1 := h7701c.2.1
                                      have p7701_2 := h7701c.2.2.1
                                      have p7701_3 := h7701c.2.2.2
                                      linarith only [hlam, p7701_0]
                            · linarith only [h7606, h7607, h7694, hc23, hc35, hlam, hphi]
                      · linarith only [h7606, h7607, h7689, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h7602, h7688, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h7602, h7687, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h7602, h7686, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7750 | h7750
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7751 | h7751
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7752 | h7752
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7753 | h7753
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7754 | h7754
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7755 | h7755
                      · linarith only [h7600, h7606, h7750, h7755, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7757 | h7757
                        · linarith only [h0, h7601, h7755, h7757, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h7606, h7750, h7752, h7757, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h7600, h7750, h7754, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h7601, h7606, h7750, h7753, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h0, h7601, h7606, h7750, h7752, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h7606, h7750, h7751, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7764 | h7764
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7765 | h7765
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7766 | h7766
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7767 | h7767
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7768 | h7768
                      · linarith only [h7600, h7606, h7768, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7770 | h7770
                        · linarith only [h7600, h7750, h7770, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7772 | h7772
                          · linarith only [h0, h7601, h7772, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7774 | h7774
                            · linarith only [h7606, h7764, h7765, h7768, h7772, h7774, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7776 | h7776
                              · linarith only [h7750, h7764, h7765, h7768, h7772, h7776, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7778 | h7778
                                · linarith only [h7766, h7772, h7778, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7780 | h7780
                                  · rcases h0bigk with h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [hlam, p7781_0]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h0, hlam, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      rcases p7781_3 (m.d 0 1) (by simp) with h7784 | h7784
                                      · rcases p7781_3 (m.d 0 2) (by simp) with h7785 | h7785
                                        · rcases p7781_3 (m.d 0 3) (by simp) with h7786 | h7786
                                          · linarith only [h7600, h7786, hlam]
                                          · rcases p7781_3 (m.d 0 4) (by simp) with h7788 | h7788
                                            · linarith only [h7601, h7788, hlam]
                                            · linarith only [h7606, h7788, hlam]
                                        · linarith only [h7603, h7785, hlam]
                                      · linarith only [h7600, h7784, hlam]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h0, h7764, h7768, h7772, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p7781_1, u5ehi0]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h0, h7601, h7764, h7765, h7768, h7772, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [hlam, p7781_0]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      rcases p7781_3 (m.d 0 1) (by simp) with h7797 | h7797
                                      · linarith only [h0, h7797, hlam]
                                      · linarith only [h7600, h7797, hlam]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7764, h7765, h7768, h7772, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      rcases p7781_3 (m.d 0 1) (by simp) with h7801 | h7801
                                      · linarith only [h0, h7801, hlam]
                                      · linarith only [h7602, h7801, hlam]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7600, hlam, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7603, hlam, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [hlam, p7781_0]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7606, hlam, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7750, hlam, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7601, hlam, p7781_0]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7604, hlam, p7781_0]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      rcases p7781_3 (m.d 0 1) (by simp) with h7811 | h7811
                                      · rcases p7781_3 (m.d 0 2) (by simp) with h7812 | h7812
                                        · rcases p7781_3 (m.d 0 3) (by simp) with h7813 | h7813
                                          · linarith only [h7606, h7813, hlam]
                                          · rcases p7781_3 (m.d 0 4) (by simp) with h7815 | h7815
                                            · rcases p7781_3 (m.d 0 5) (by simp) with h7816 | h7816
                                              · linarith only [h7764, h7816, hlam]
                                              · linarith only [h7750, h7816, hlam]
                                            · linarith only [h7606, h7815, hlam]
                                        · linarith only [h7603, h7812, hlam]
                                      · linarith only [h7600, h7811, hlam]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [hlam, p7781_0]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7606, h7764, h7765, h7768, h7772, hc23, hc34, hlam, hphi, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7602, hlam, p7781_0]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7605, hlam, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      rcases p7781_3 (m.d 0 1) (by simp) with h7826 | h7826
                                      · rcases p7781_3 (m.d 0 2) (by simp) with h7827 | h7827
                                        · rcases p7781_3 (m.d 0 3) (by simp) with h7828 | h7828
                                          · linarith only [h7750, h7828, hlam]
                                          · rcases p7781_3 (m.d 0 4) (by simp) with h7830 | h7830
                                            · rcases p7781_3 (m.d 0 5) (by simp) with h7831 | h7831
                                              · rcases h2bigk with h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h0, hlam, p7832_1]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  rcases p7832_3 (m.d 0 2) (by simp) with h7835 | h7835
                                                  · rcases p7832_3 (m.d 1 2) (by simp) with h7836 | h7836
                                                    · rcases p7832_3 (m.d 2 3) (by simp) with h7837 | h7837
                                                      · linarith only [h7837, hlam, p7832_0]
                                                      · rcases p7832_3 (m.d 2 4) (by simp) with h7839 | h7839
                                                        · linarith only [h7604, h7839, hlam]
                                                        · linarith only [h7774, h7839, hlam]
                                                    · linarith only [h7765, h7836, hlam]
                                                  · linarith only [h7835, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  rcases p7832_3 (m.d 0 2) (by simp) with h7844 | h7844
                                                  · rcases p7832_3 (m.d 1 2) (by simp) with h7845 | h7845
                                                    · rcases p7832_3 (m.d 2 3) (by simp) with h7846 | h7846
                                                      · linarith only [h7603, h7846, hlam]
                                                      · rcases p7832_3 (m.d 2 4) (by simp) with h7848 | h7848
                                                        · linarith only [h7848, hlam, p7832_0]
                                                        · rcases p7832_3 (m.d 2 5) (by simp) with h7850 | h7850
                                                          · linarith only [h7605, h7850, hlam]
                                                          · linarith only [h7778, h7850, hlam]
                                                    · linarith only [h7766, h7845, hlam]
                                                  · linarith only [h7844, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  rcases p7832_3 (m.d 0 2) (by simp) with h7855 | h7855
                                                  · rcases p7832_3 (m.d 1 2) (by simp) with h7856 | h7856
                                                    · rcases p7832_3 (m.d 2 3) (by simp) with h7857 | h7857
                                                      · linarith only [h7603, h7857, hlam]
                                                      · rcases p7832_3 (m.d 2 4) (by simp) with h7859 | h7859
                                                        · linarith only [h7604, h7859, hlam]
                                                        · rcases p7832_3 (m.d 2 5) (by simp) with h7861 | h7861
                                                          · linarith only [h7861, hlam, p7832_0]
                                                          · rcases h3bigk with h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c | h7863c
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7765, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7781_1, p7863_1]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h0, h7602, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7781_1, p7863_1]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7606, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7750, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7600, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7768, h7772, hc23, hc45, hlam, hphi, ht34, p7863_1]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7768, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7770, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7603, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7765, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7774, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7776, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              rcases p7863_3 (m.d 0 3) (by simp) with h7879 | h7879
                                                              · linarith only [h7879, hlam, p7863_0]
                                                              · rcases p7863_3 (m.d 1 3) (by simp) with h7881 | h7881
                                                                · linarith only [h7768, h7881, hlam]
                                                                · rcases p7863_3 (m.d 2 3) (by simp) with h7883 | h7883
                                                                  · linarith only [h7774, h7883, hlam]
                                                                  · rcases p7863_3 (m.d 3 4) (by simp) with h7885 | h7885
                                                                    · rcases p7863_3 (m.d 3 5) (by simp) with h7886 | h7886
                                                                      · linarith only [h7780, h7886, hlam]
                                                                      · linarith only [h7750, h7886, hlam]
                                                                    · linarith only [h7885, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              rcases p7863_3 (m.d 0 3) (by simp) with h7890 | h7890
                                                              · linarith only [h7606, h7890, hlam]
                                                              · linarith only [h7600, h7890, hlam]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              rcases p7863_3 (m.d 0 3) (by simp) with h7893 | h7893
                                                              · linarith only [h7606, h7893, hlam]
                                                              · linarith only [h7603, h7893, hlam]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7750, hc03, hc34, hlam, hphi, p7863_1]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              rcases p7863_3 (m.d 0 3) (by simp) with h7898 | h7898
                                                              · linarith only [h7898, hlam, p7863_0]
                                                              · rcases p7863_3 (m.d 1 3) (by simp) with h7900 | h7900
                                                                · linarith only [h7770, h7900, hlam]
                                                                · rcases p7863_3 (m.d 2 3) (by simp) with h7902 | h7902
                                                                  · linarith only [h7776, h7902, hlam]
                                                                  · rcases p7863_3 (m.d 3 4) (by simp) with h7904 | h7904
                                                                    · rcases p7863_3 (m.d 3 5) (by simp) with h7905 | h7905
                                                                      · rcases h5bigk with h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c | h7906c
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [hlam, p7906_0]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h0, h7602, h7767, hc12, hlam, hphi, ht01, ht0b, ht5b, p7906_1, u5ehi2]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h0, h7602, hc12, hlam, hphi, ht01, ht0b, ht5b, p7906_1, u5ehi2]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7750, hlam, p7906_1]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h0, h7601, h7764, h7772, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7906_1]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7602, hlam, p7906_0]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [hlam, p7906_0]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h0, h7602, hc12, hlam, hphi, ht01, ht0b, ht5b, p7906_1, u5ehi2]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7770, hlam, p7906_1]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7772, hlam, p7906_1]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7605, hlam, p7906_1]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7767, hlam, p7906_1]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [hlam, p7906_0]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7776, hlam, p7906_1]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7778, hlam, p7906_1]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7600, h7765, hc23, hc35, hlam, hphi, p7781_1, p7906_1]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          rcases p7906_3 (m.d 0 5) (by simp) with h7923 | h7923
                                                                          · linarith only [h7750, h7923, hlam]
                                                                          · linarith only [h7602, h7923, hlam]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          rcases p7906_3 (m.d 0 5) (by simp) with h7926 | h7926
                                                                          · linarith only [h7750, h7926, hlam]
                                                                          · linarith only [h7605, h7926, hlam]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [hlam, p7906_0]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7765, h7768, h7772, h7780, hc23, hc34, hlam, hphi, p7906_1]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7764, hlam, p7906_0]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h0, h7601, h7764, h7767, hc12, hlam, hphi, ht01, ht0b, ht5b, p7906_1, u5ehi2]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h0, h7601, h7764, hc12, hlam, hphi, ht01, ht0b, ht5b, p7906_1, u5ehi2]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [h7780, hlam, p7906_0]
                                                                        · have p7906_0 := h7906c.1
                                                                          have p7906_1 := h7906c.2.1
                                                                          have p7906_2 := h7906c.2.2.1
                                                                          have p7906_3 := h7906c.2.2.2
                                                                          linarith only [hlam, p7906_0]
                                                                      · linarith only [h7905, hlam, p7863_0]
                                                                    · linarith only [h7606, h7904, hlam]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              rcases p7863_3 (m.d 0 3) (by simp) with h7938 | h7938
                                                              · linarith only [h7750, h7938, hlam]
                                                              · linarith only [h7600, h7938, hlam]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              rcases p7863_3 (m.d 0 3) (by simp) with h7941 | h7941
                                                              · linarith only [h7750, h7941, hlam]
                                                              · linarith only [h7603, h7941, hlam]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [h7780, hlam, p7863_0]
                                                            · have p7863_0 := h7863c.1
                                                              have p7863_1 := h7863c.2.1
                                                              have p7863_2 := h7863c.2.2.1
                                                              have p7863_3 := h7863c.2.2.2
                                                              linarith only [hlam, p7863_0]
                                                    · linarith only [h7767, h7856, hlam]
                                                  · linarith only [h7855, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h0, h7601, h7764, hc12, hlam, hphi, ht01, ht0b, ht5b, p7832_1, u5ehi4]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h0, h7600, h7601, h7764, h7765, hlam, p7781_1, p7832_2]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h0, h7601, h7764, h7766, h7772, hlam, p7832_2]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  rcases p7832_3 (m.d 0 2) (by simp) with h7952 | h7952
                                                  · linarith only [h0, h7952, hlam]
                                                  · linarith only [h7605, h7952, hlam]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h7603, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h7765, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h7774, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h7776, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h7604, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h7766, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h7601, h7764, h7766, h7772, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7832_1]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h7778, hlam, p7832_1]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h7605, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h7767, hlam, p7832_0]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h0, h7602, h7767, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7832_1]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [h0, h7601, h7764, h7767, h7772, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7832_1]
                                                · have p7832_0 := h7832c.1
                                                  have p7832_1 := h7832c.2.1
                                                  have p7832_2 := h7832c.2.2.1
                                                  have p7832_3 := h7832c.2.2.2
                                                  linarith only [hlam, p7832_0]
                                              · linarith only [h7750, h7831, hlam]
                                            · linarith only [h7606, h7830, hlam]
                                        · linarith only [h7603, h7827, hlam]
                                      · linarith only [h7600, h7826, hlam]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [h7764, hlam, p7781_1]
                                    · have p7781_0 := h7781c.1
                                      have p7781_1 := h7781c.2.1
                                      have p7781_2 := h7781c.2.2.1
                                      have p7781_3 := h7781c.2.2.2
                                      linarith only [hlam, p7781_0]
                                  · linarith only [h0, h7600, h7601, h7606, h7764, h7765, h7780, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h7601, h7764, h7767, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h7601, h7764, h7766, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h7601, h7764, h7765, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7980 | h7980
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7981 | h7981
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7982 | h7982
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7983 | h7983
                      · linarith only [h7600, h7606, h7983, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7985 | h7985
                        · linarith only [h0, h7600, h7985, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7987 | h7987
                          · linarith only [h0, h7601, h7606, h7764, h7987, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7989 | h7989
                            · linarith only [h7600, h7606, h7980, h7989, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7991 | h7991
                              · linarith only [h0, h7600, h7750, h7980, h7991, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7993 | h7993
                                · linarith only [h0, h7601, h7764, h7981, h7993, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7995 | h7995
                                  · rcases h0bigk with h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c | h7996c
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [hlam, p7996_0]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h0, hlam, p7996_1]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      rcases p7996_3 (m.d 0 1) (by simp) with h7999 | h7999
                                      · rcases p7996_3 (m.d 0 2) (by simp) with h8000 | h8000
                                        · rcases p7996_3 (m.d 0 3) (by simp) with h8001 | h8001
                                          · linarith only [h7600, h8001, hlam]
                                          · rcases p7996_3 (m.d 0 4) (by simp) with h8003 | h8003
                                            · linarith only [h7601, h8003, hlam]
                                            · linarith only [h7606, h8003, hlam]
                                        · linarith only [h7603, h8000, hlam]
                                      · linarith only [h7600, h7999, hlam]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      rcases p7996_3 (m.d 0 1) (by simp) with h8008 | h8008
                                      · rcases p7996_3 (m.d 0 2) (by simp) with h8009 | h8009
                                        · rcases p7996_3 (m.d 0 3) (by simp) with h8010 | h8010
                                          · linarith only [h7600, h8010, hlam]
                                          · rcases p7996_3 (m.d 0 4) (by simp) with h8012 | h8012
                                            · linarith only [h7601, h8012, hlam]
                                            · rcases p7996_3 (m.d 0 5) (by simp) with h8014 | h8014
                                              · linarith only [h7602, h8014, hlam]
                                              · linarith only [h7764, h8014, hlam]
                                        · linarith only [h7604, h8009, hlam]
                                      · linarith only [h7601, h8008, hlam]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h0, h7602, h7982, hc12, hlam, hphi, ht01, ht0b, ht5b, p7996_1, u5ehi2]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h0, h7602, h7982, hc12, hlam, hphi, ht01, ht0b, ht5b, p7996_1, u5ehi2]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [hlam, p7996_0]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      rcases p7996_3 (m.d 0 1) (by simp) with h8022 | h8022
                                      · linarith only [h0, h8022, hlam]
                                      · linarith only [h7600, h8022, hlam]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      rcases p7996_3 (m.d 0 1) (by simp) with h8025 | h8025
                                      · linarith only [h0, h8025, hlam]
                                      · linarith only [h7601, h8025, hlam]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      rcases p7996_3 (m.d 0 1) (by simp) with h8028 | h8028
                                      · linarith only [h0, h8028, hlam]
                                      · linarith only [h7602, h8028, hlam]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7600, hlam, p7996_1]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7603, hlam, p7996_1]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [hlam, p7996_0]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7606, hlam, p7996_1]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7750, hlam, p7996_1]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7601, hlam, p7996_0]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7604, hlam, p7996_0]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7600, h7764, h7980, h7995, hc23, hc34, hlam, hphi, p7996_1]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [hlam, p7996_0]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7764, hlam, p7996_0]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7602, hlam, p7996_0]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7605, hlam, p7996_1]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7600, h7764, h7980, h7995, hc23, hc34, hlam, hphi, p7996_1]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [h7600, h7606, h7764, h7980, h7995, hc23, hc34, hlam, hphi, p7996_1]
                                    · have p7996_0 := h7996c.1
                                      have p7996_1 := h7996c.2.1
                                      have p7996_2 := h7996c.2.2.1
                                      have p7996_3 := h7996c.2.2.2
                                      linarith only [hlam, p7996_0]
                                  · rcases h0bigk with h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c | h8046c
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [hlam, p8046_0]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h0, hlam, p8046_1]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      rcases p8046_3 (m.d 0 1) (by simp) with h8049 | h8049
                                      · rcases p8046_3 (m.d 0 2) (by simp) with h8050 | h8050
                                        · rcases p8046_3 (m.d 0 3) (by simp) with h8051 | h8051
                                          · linarith only [h7600, h8051, hlam]
                                          · rcases p8046_3 (m.d 0 4) (by simp) with h8053 | h8053
                                            · linarith only [h7601, h8053, hlam]
                                            · linarith only [h7606, h8053, hlam]
                                        · linarith only [h7603, h8050, hlam]
                                      · linarith only [h7600, h8049, hlam]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      rcases p8046_3 (m.d 0 1) (by simp) with h8058 | h8058
                                      · rcases p8046_3 (m.d 0 2) (by simp) with h8059 | h8059
                                        · rcases p8046_3 (m.d 0 3) (by simp) with h8060 | h8060
                                          · linarith only [h7600, h8060, hlam]
                                          · rcases p8046_3 (m.d 0 4) (by simp) with h8062 | h8062
                                            · linarith only [h7601, h8062, hlam]
                                            · rcases p8046_3 (m.d 0 5) (by simp) with h8064 | h8064
                                              · linarith only [h7602, h8064, hlam]
                                              · linarith only [h7764, h8064, hlam]
                                        · linarith only [h7604, h8059, hlam]
                                      · linarith only [h7601, h8058, hlam]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p8046_1, u5ehi0]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7602, h7982, hc02, hlam, hphi, ht0b, ht5b, p8046_1, u5ehi2]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [hlam, p8046_0]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      rcases p8046_3 (m.d 0 1) (by simp) with h8072 | h8072
                                      · linarith only [h0, h8072, hlam]
                                      · linarith only [h7600, h8072, hlam]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      rcases p8046_3 (m.d 0 1) (by simp) with h8075 | h8075
                                      · linarith only [h0, h8075, hlam]
                                      · linarith only [h7601, h8075, hlam]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      rcases p8046_3 (m.d 0 1) (by simp) with h8078 | h8078
                                      · linarith only [h0, h8078, hlam]
                                      · linarith only [h7602, h8078, hlam]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7600, hlam, p8046_1]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7603, hlam, p8046_1]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [hlam, p8046_0]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7606, hlam, p8046_1]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7750, hlam, p8046_1]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7601, hlam, p8046_0]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7604, hlam, p8046_0]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7600, h7606, h7980, h7995, hc23, hc45, hlam, hphi, ht34, p8046_1]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [hlam, p8046_0]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7764, hlam, p8046_0]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7602, hlam, p8046_0]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [h7605, hlam, p8046_1]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      rcases p8046_3 (m.d 0 1) (by simp) with h8093 | h8093
                                      · rcases p8046_3 (m.d 0 2) (by simp) with h8094 | h8094
                                        · rcases p8046_3 (m.d 0 3) (by simp) with h8095 | h8095
                                          · linarith only [h7750, h8095, hlam]
                                          · rcases p8046_3 (m.d 0 4) (by simp) with h8097 | h8097
                                            · linarith only [h7764, h8097, hlam]
                                            · linarith only [h7606, h8097, hlam]
                                        · linarith only [h7603, h8094, hlam]
                                      · linarith only [h7600, h8093, hlam]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      rcases p8046_3 (m.d 0 1) (by simp) with h8102 | h8102
                                      · rcases p8046_3 (m.d 0 2) (by simp) with h8103 | h8103
                                        · rcases p8046_3 (m.d 0 3) (by simp) with h8104 | h8104
                                          · linarith only [h7750, h8104, hlam]
                                          · rcases p8046_3 (m.d 0 4) (by simp) with h8106 | h8106
                                            · linarith only [h7764, h8106, hlam]
                                            · rcases p8046_3 (m.d 0 5) (by simp) with h8108 | h8108
                                              · rcases h2bigk with h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c | h8109c
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h0, hlam, p8109_1]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  rcases p8109_3 (m.d 0 2) (by simp) with h8112 | h8112
                                                  · rcases p8109_3 (m.d 1 2) (by simp) with h8113 | h8113
                                                    · rcases p8109_3 (m.d 2 3) (by simp) with h8114 | h8114
                                                      · linarith only [h8114, hlam, p8109_0]
                                                      · rcases p8109_3 (m.d 2 4) (by simp) with h8116 | h8116
                                                        · linarith only [h7604, h8116, hlam]
                                                        · linarith only [h7989, h8116, hlam]
                                                    · linarith only [h7980, h8113, hlam]
                                                  · linarith only [h8112, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  rcases p8109_3 (m.d 0 2) (by simp) with h8121 | h8121
                                                  · rcases p8109_3 (m.d 1 2) (by simp) with h8122 | h8122
                                                    · rcases p8109_3 (m.d 2 3) (by simp) with h8123 | h8123
                                                      · linarith only [h7603, h8123, hlam]
                                                      · rcases p8109_3 (m.d 2 4) (by simp) with h8125 | h8125
                                                        · linarith only [h8125, hlam, p8109_0]
                                                        · rcases p8109_3 (m.d 2 5) (by simp) with h8127 | h8127
                                                          · linarith only [h7605, h8127, hlam]
                                                          · linarith only [h7993, h8127, hlam]
                                                    · linarith only [h7981, h8122, hlam]
                                                  · linarith only [h8121, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  rcases p8109_3 (m.d 0 2) (by simp) with h8132 | h8132
                                                  · rcases p8109_3 (m.d 1 2) (by simp) with h8133 | h8133
                                                    · rcases p8109_3 (m.d 2 3) (by simp) with h8134 | h8134
                                                      · linarith only [h7603, h8134, hlam]
                                                      · rcases p8109_3 (m.d 2 4) (by simp) with h8136 | h8136
                                                        · linarith only [h7604, h8136, hlam]
                                                        · rcases p8109_3 (m.d 2 5) (by simp) with h8138 | h8138
                                                          · linarith only [h8138, hlam, p8109_0]
                                                          · rcases h3bigk with h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c | h8140c
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7602, h7606, h7980, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8046_1, p8140_1]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h0, h7602, h7606, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8046_1, p8140_1]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7606, hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7750, hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7600, hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h0, h7600, h7602, h7606, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8046_1, p8140_1]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7983, hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7985, hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7603, hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7980, hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7989, hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7991, hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7995, hc03, hc45, hlam, hphi, ht34, p8140_1]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7980, h7995, hc23, hc45, hlam, hphi, ht34, p8140_1]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7995, hc23, hc45, hlam, hphi, ht34, p8140_1]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [hlam, p8140_0]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7995, hlam, p8140_1]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              rcases p8140_3 (m.d 0 3) (by simp) with h8161 | h8161
                                                              · linarith only [h8161, hlam, p8140_0]
                                                              · rcases p8140_3 (m.d 1 3) (by simp) with h8163 | h8163
                                                                · linarith only [h7985, h8163, hlam]
                                                                · rcases p8140_3 (m.d 2 3) (by simp) with h8165 | h8165
                                                                  · linarith only [h7991, h8165, hlam]
                                                                  · rcases p8140_3 (m.d 3 4) (by simp) with h8167 | h8167
                                                                    · linarith only [h7995, h8167, hlam]
                                                                    · linarith only [h7606, h8167, hlam]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              rcases p8140_3 (m.d 0 3) (by simp) with h8170 | h8170
                                                              · linarith only [h7750, h8170, hlam]
                                                              · linarith only [h7600, h8170, hlam]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              rcases p8140_3 (m.d 0 3) (by simp) with h8173 | h8173
                                                              · linarith only [h7750, h8173, hlam]
                                                              · linarith only [h7603, h8173, hlam]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [h7600, h7606, h7980, h7995, hc23, hc45, hlam, hphi, ht34, p8140_1]
                                                            · have p8140_0 := h8140c.1
                                                              have p8140_1 := h8140c.2.1
                                                              have p8140_2 := h8140c.2.2.1
                                                              have p8140_3 := h8140c.2.2.2
                                                              linarith only [hlam, p8140_0]
                                                    · linarith only [h7982, h8133, hlam]
                                                  · linarith only [h8132, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h0, h7602, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8046_1, p8109_1]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h0, h7600, h7602, h7606, h7980, hlam, p8046_1, p8109_2]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h0, h7601, h7602, h7981, hlam, p8046_1, p8109_2]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  rcases p8109_3 (m.d 0 2) (by simp) with h8184 | h8184
                                                  · linarith only [h0, h8184, hlam]
                                                  · linarith only [h7605, h8184, hlam]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h7603, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h7980, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h7989, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h7991, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h7604, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h7981, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h7601, h7602, h7981, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8046_1, p8109_1]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h7993, hlam, p8109_1]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h7605, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h7982, hlam, p8109_0]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h0, h7602, h7982, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8109_1]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [h0, h7602, h7982, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8109_1]
                                                · have p8109_0 := h8109c.1
                                                  have p8109_1 := h8109c.2.1
                                                  have p8109_2 := h8109c.2.2.1
                                                  have p8109_3 := h8109c.2.2.2
                                                  linarith only [hlam, p8109_0]
                                              · linarith only [h7764, h8108, hlam]
                                        · linarith only [h7604, h8103, hlam]
                                      · linarith only [h7601, h8102, hlam]
                                    · have p8046_0 := h8046c.1
                                      have p8046_1 := h8046c.2.1
                                      have p8046_2 := h8046c.2.2.1
                                      have p8046_3 := h8046c.2.2.2
                                      linarith only [hlam, p8046_0]
                    · linarith only [h0, h7602, h7982, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h7602, h7981, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h7602, h7980, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
        · linarith only [h0, h7602, h7605, hlam]
      · linarith only [h0, h7601, h7604, hlam]
    · linarith only [h0, h7600, h7603, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h8212 | h8212
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8213 | h8213
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8214 | h8214
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8215 | h8215
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8216 | h8216
            · linarith only [h7600, h7602, h8216, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8218 | h8218
              · linarith only [h7600, h7602, h8215, h8218, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8220 | h8220
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8221 | h8221
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8222 | h8222
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8223 | h8223
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8224 | h8224
                        · linarith only [h7600, h7602, h8216, h8222, h8224, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8226 | h8226
                          · linarith only [h7600, h7602, h8218, h8223, h8226, hlam]
                          · linarith only [h7600, h7602, h8223, h8226, hc34, hc45, hlam, hphi]
                      · linarith only [h8215, h8216, h8220, h8223, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h8214, h8222, hlam]
                  · linarith only [h0, h8213, h8221, hlam]
                · linarith only [h0, h7600, h8212, h8215, h8220, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8233 | h8233
            · linarith only [h7601, h7602, h8215, h8233, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8235 | h8235
              · linarith only [h7601, h7602, h8235, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8237 | h8237
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8238 | h8238
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8239 | h8239
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8240 | h8240
                      · linarith only [h7600, h7602, h8215, h8239, h8240, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8242 | h8242
                        · linarith only [h7600, h7602, h8233, h8242, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8244 | h8244
                          · linarith only [h7600, h7601, h7602, h8215, h8235, h8242, h8244, hc13, hc35, hlam, hphi]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8246 | h8246
                            · linarith only [h7600, h7602, h8237, h8244, h8246, hc34, hc45, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8248 | h8248
                              · linarith only [h7601, h7602, h8237, h8240, h8244, h8248, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8250 | h8250
                                · linarith only [h7601, h7602, h8238, h8244, h8250, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8252 | h8252
                                  · linarith only [h7601, h7602, h8240, h8244, h8252, hc13, hc34, hlam, hphi]
                                  · rcases h0bigk with h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h0, hlam, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7602, h8242, hc03, hc35, hlam, hphi, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7600, h7602, h8215, h8237, h8242, hc23, hc35, hlam, hphi, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7602, hlam, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      rcases p8254_3 (m.d 0 1) (by simp) with h8260 | h8260
                                      · linarith only [h0, h8260, hlam]
                                      · rcases p8254_3 (m.d 0 2) (by simp) with h8262 | h8262
                                        · rcases p8254_3 (m.d 0 3) (by simp) with h8263 | h8263
                                          · linarith only [h8212, h8263, hlam]
                                          · rcases p8254_3 (m.d 0 4) (by simp) with h8265 | h8265
                                            · linarith only [h8213, h8265, hlam]
                                            · rcases p8254_3 (m.d 0 5) (by simp) with h8267 | h8267
                                              · linarith only [h8214, h8267, hlam]
                                              · linarith only [h7602, h8267, hlam]
                                        · linarith only [h0, h8262, hlam]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      rcases p8254_3 (m.d 0 1) (by simp) with h8272 | h8272
                                      · linarith only [h0, h8272, hlam]
                                      · linarith only [h7600, h8272, hlam]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      rcases p8254_3 (m.d 0 1) (by simp) with h8275 | h8275
                                      · linarith only [h0, h8275, hlam]
                                      · linarith only [h7601, h8275, hlam]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      rcases p8254_3 (m.d 0 1) (by simp) with h8278 | h8278
                                      · linarith only [h0, h8278, hlam]
                                      · rcases p8254_3 (m.d 0 2) (by simp) with h8280 | h8280
                                        · rcases p8254_3 (m.d 0 3) (by simp) with h8281 | h8281
                                          · linarith only [h8212, h8281, hlam]
                                          · rcases p8254_3 (m.d 0 4) (by simp) with h8283 | h8283
                                            · linarith only [h8213, h8283, hlam]
                                            · rcases p8254_3 (m.d 0 5) (by simp) with h8285 | h8285
                                              · linarith only [h8214, h8285, hlam]
                                              · rcases h2bigk with h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h0, hlam, p8287_1]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h7600, h7602, h8237, hlam, p8254_1, p8287_2]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h7601, h7602, h8238, hlam, p8254_1, p8287_2]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  rcases p8287_3 (m.d 0 2) (by simp) with h8292 | h8292
                                                  · rcases p8287_3 (m.d 1 2) (by simp) with h8293 | h8293
                                                    · rcases p8287_3 (m.d 2 3) (by simp) with h8294 | h8294
                                                      · linarith only [h8212, h8294, hlam]
                                                      · rcases p8287_3 (m.d 2 4) (by simp) with h8296 | h8296
                                                        · linarith only [h8213, h8296, hlam]
                                                        · rcases p8287_3 (m.d 2 5) (by simp) with h8298 | h8298
                                                          · linarith only [h8298, hlam, p8287_0]
                                                          · rcases h3bigk with h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h7600, h7602, h8237, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8254_1, p8300_1]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h0, h7601, h7602, h8215, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8254_1, p8300_1]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8215, hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8233, hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h7600, hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h0, h7600, h7602, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8254_1, p8300_1]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8240, hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8242, hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8212, hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8237, hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8246, hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8248, hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8252, hc03, hc45, hlam, hphi, ht34, p8300_1]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8237, h8252, hc23, hc45, hlam, hphi, ht34, p8300_1]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8252, hc23, hc45, hlam, hphi, ht34, p8300_1]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [hlam, p8300_0]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h8252, hlam, p8300_1]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              rcases p8300_3 (m.d 0 3) (by simp) with h8321 | h8321
                                                              · linarith only [h8321, hlam, p8300_0]
                                                              · rcases p8300_3 (m.d 1 3) (by simp) with h8323 | h8323
                                                                · linarith only [h8242, h8323, hlam]
                                                                · rcases p8300_3 (m.d 2 3) (by simp) with h8325 | h8325
                                                                  · linarith only [h8248, h8325, hlam]
                                                                  · rcases p8300_3 (m.d 3 4) (by simp) with h8327 | h8327
                                                                    · linarith only [h8252, h8327, hlam]
                                                                    · linarith only [h8215, h8327, hlam]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              rcases p8300_3 (m.d 0 3) (by simp) with h8330 | h8330
                                                              · linarith only [h8233, h8330, hlam]
                                                              · linarith only [h7600, h8330, hlam]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              rcases p8300_3 (m.d 0 3) (by simp) with h8333 | h8333
                                                              · linarith only [h8233, h8333, hlam]
                                                              · linarith only [h8212, h8333, hlam]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [h7600, h8215, h8237, h8252, hc23, hc45, hlam, hphi, ht34, p8300_1]
                                                            · have p8300_0 := h8300c.1
                                                              have p8300_1 := h8300c.2.1
                                                              have p8300_2 := h8300c.2.2.1
                                                              have p8300_3 := h8300c.2.2.2
                                                              linarith only [hlam, p8300_0]
                                                    · linarith only [h8239, h8293, hlam]
                                                  · linarith only [h8292, hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h7602, hc01, hc12, hlam, hphi, p8254_1, p8287_1]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h0, h7600, h7602, h8237, hlam, p8254_1, p8287_2]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h0, h7601, h7602, h8238, hlam, p8254_1, p8287_2]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  rcases p8287_3 (m.d 0 2) (by simp) with h8344 | h8344
                                                  · linarith only [h0, h8344, hlam]
                                                  · linarith only [h8214, h8344, hlam]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h8212, hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h8237, hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h8246, hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h8248, hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h8213, hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h8238, hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h7601, h7602, h8238, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8254_1, p8287_1]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h8250, hlam, p8287_1]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h8214, hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h8239, hlam, p8287_0]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h0, h8214, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8254_1, p8287_1]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [h0, h8214, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8254_1, p8287_1]
                                                · have p8287_0 := h8287c.1
                                                  have p8287_1 := h8287c.2.1
                                                  have p8287_2 := h8287c.2.2.1
                                                  have p8287_3 := h8287c.2.2.2
                                                  linarith only [hlam, p8287_0]
                                        · linarith only [h8214, h8280, hlam]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7600, hlam, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8212, hlam, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8215, hlam, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8233, hlam, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7601, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8213, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7600, h7601, h7602, h8237, h8242, h8252, hc23, hc45, hlam, hphi, ht34, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8235, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7601, h7602, h8242, h8252, hc14, hc45, hlam, hphi, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8214, hlam, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      rcases p8254_3 (m.d 0 1) (by simp) with h8375 | h8375
                                      · linarith only [h7602, h8375, hlam]
                                      · linarith only [h7600, h8375, hlam]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      rcases p8254_3 (m.d 0 1) (by simp) with h8378 | h8378
                                      · linarith only [h7602, h8378, hlam]
                                      · linarith only [h7601, h8378, hlam]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [hlam, p8254_0]
                    · linarith only [h0, h8214, h8239, hlam]
                  · linarith only [h0, h8213, h8238, hlam]
                · linarith only [h0, h8212, h8237, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8385 | h8385
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8386 | h8386
            · linarith only [h0, h7600, h8214, h8386, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8388 | h8388
              · linarith only [h7601, h7602, h8388, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8390 | h8390
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8391 | h8391
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8392 | h8392
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8393 | h8393
                      · linarith only [h0, h7600, h8214, h8392, h8393, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h7600, h8214, h8385, h8392, h8393, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8396 | h8396
                      · linarith only [h0, h7600, h8392, h8396, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h7600, h8385, h8392, h8396, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h7601, h8213, h8214, h8391, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h8212, h8390, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8401 | h8401
            · linarith only [h7600, h7602, h8401, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8403 | h8403
              · linarith only [h0, h7601, h8214, h8403, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8405 | h8405
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8406 | h8406
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8407 | h8407
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8408 | h8408
                      · linarith only [h0, h7600, h8214, h8385, h8407, h8408, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8410 | h8410
                        · linarith only [h0, h7600, h8214, h8401, h8410, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8412 | h8412
                          · linarith only [h0, h7601, h8214, h8403, h8407, h8412, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8414 | h8414
                            · linarith only [h7600, h8385, h8405, h8414, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8416 | h8416
                              · linarith only [h0, h7601, h8214, h8405, h8407, h8408, h8416, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8418 | h8418
                                · linarith only [h0, h7601, h8214, h8406, h8407, h8412, h8418, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8420 | h8420
                                  · linarith only [h0, h7601, h8214, h8405, h8407, h8408, h8412, h8420, hc23, hc34, hlam, hphi]
                                  · rcases h0bigk with h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c | h8422c
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [hlam, p8422_0]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h0, hlam, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h0, h7600, h8214, h8405, h8407, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h0, h8214, h8407, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h7602, hlam, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h8214, h8407, hc01, hc12, hlam, hphi, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [hlam, p8422_0]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h7600, h8214, h8405, h8407, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h7601, h8214, h8406, h8407, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h8214, hlam, p8422_0]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h7600, hlam, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h8212, hlam, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [hlam, p8422_0]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h8385, hlam, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h8401, hlam, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h7601, hlam, p8422_0]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h8213, hlam, p8422_0]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h0, h7600, h7601, h8214, h8405, h8407, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [hlam, p8422_0]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h8403, hlam, p8422_0]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h7600, h7602, h8405, h8410, hc23, hc35, hlam, hphi, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [h0, h7600, h8214, h8405, h8407, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8422_1]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      rcases p8422_3 (m.d 0 1) (by simp) with h8445 | h8445
                                      · linarith only [h7602, h8445, hlam]
                                      · linarith only [h7600, h8445, hlam]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      rcases p8422_3 (m.d 0 1) (by simp) with h8448 | h8448
                                      · linarith only [h7602, h8448, hlam]
                                      · linarith only [h7601, h8448, hlam]
                                    · have p8422_0 := h8422c.1
                                      have p8422_1 := h8422c.2.1
                                      have p8422_2 := h8422c.2.2.1
                                      have p8422_3 := h8422c.2.2.2
                                      linarith only [hlam, p8422_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8452 | h8452
                      · linarith only [h0, h7600, h8407, h8452, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8454 | h8454
                        · linarith only [h0, h7601, h8407, h8452, h8454, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8456 | h8456
                          · linarith only [h0, h7601, h8403, h8407, h8456, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8458 | h8458
                            · linarith only [h7600, h8385, h8405, h8458, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8460 | h8460
                              · linarith only [h0, h7601, h8405, h8407, h8452, h8454, h8460, hlam]
                              · linarith only [h0, h7601, h8405, h8407, h8452, h8460, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h7600, h8213, h8405, h8406, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h8212, h8405, hlam]
      · linarith only [h0, h7601, h8213, hlam]
    · linarith only [h0, h7600, h8212, hlam]

end R2N4
