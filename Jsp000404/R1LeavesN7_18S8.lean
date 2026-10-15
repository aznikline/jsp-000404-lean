import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9918000 in
set_option maxHeartbeats 9918000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s2 m hb0 hb2 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4674 | h4674
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4675 | h4675
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4676 | h4676
        · linarith only [h0, h2, h4676, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4678 | h4678
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4679 | h4679
            · linarith only [h1, h2, h4679, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4681 | h4681
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4682 | h4682
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4683 | h4683
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4684 | h4684
                    · linarith only [h0, h2, h4676, h4678, h4684, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4686 | h4686
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4687 | h4687
                        · linarith only [h0, h2, h4679, h4683, h4684, h4687, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h2, h4683, h4687, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h4678, h4683, h4684, h4686, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h4675, h4676, h4683, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h4681, h4682, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4693 | h4693
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4694 | h4694
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4695 | h4695
                    · linarith only [h0, h2, h4676, h4695, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4697 | h4697
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4698 | h4698
                        · linarith only [h1, h4679, h4698, hlam]
                        · linarith only [h0, h2, h4694, h4698, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h4678, h4694, h4697, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h4675, h4676, h4694, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h4678, h4693, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4704 | h4704
            · linarith only [h1, h2, h4704, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4706 | h4706
              · linarith only [h4675, h4678, h4706, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4708 | h4708
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4709 | h4709
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4710 | h4710
                    · linarith only [h0, h2, h4676, h4710, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4712 | h4712
                      · linarith only [h0, h4678, h4712, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4714 | h4714
                        · linarith only [h1, h2, h4704, h4710, h4714, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h2, h4709, h4714, hc23, hc34, hlam, hphi]
                  · linarith only [h4675, h4676, h4709, hc12, hc24, hlam, hphi]
                · linarith only [h2, h4674, h4708, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4719 | h4719
        · linarith only [h0, h2, h4719, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4721 | h4721
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4722 | h4722
            · linarith only [h1, h2, h4722, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4724 | h4724
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4725 | h4725
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4726 | h4726
                  · linarith only [h0, h2, h4675, h4726, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4728 | h4728
                    · linarith only [h0, h2, h4719, h4728, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4730 | h4730
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4731 | h4731
                        · linarith only [h1, h2, h4722, h4731, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4733 | h4733
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4734 | h4734
                            · linarith only [h1, h2, h4726, h4730, h4731, h4734, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4736 | h4736
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4737 | h4737
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4738 | h4738
                                  · rcases h0bigk with h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [hlam, p4739_0]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h0, h2, h4728, h4730, h4734, h4736, h4738, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h0, h2, h4675, h4728, h4730, h4734, h4736, h4738, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h2, hlam, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h2, h4728, h4734, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h0, hlam, p4739_0]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [hlam, p4739_0]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h4675, hlam, p4739_0]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h4719, hlam, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h0, h2, h4674, h4728, h4734, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h1, hlam, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h0, h4730, h4736, h4738, hc03, hc45, hlam, hphi, ht0b, ht5b, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [hlam, p4739_0]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h4722, hlam, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h1, h2, h4721, h4728, h4734, h4736, h4738, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h0, h4730, h4736, h4738, hc04, hc45, hlam, hphi, ht0b, ht5b, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h0, h2, h4728, h4730, h4734, h4736, h4738, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h2, h4728, h4734, hc03, hc34, hlam, hphi, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [hlam, p4739_0]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      rcases p4739_3 (m.d 0 1) (by simp) with h4759 | h4759
                                      · linarith only [h2, h4759, hlam]
                                      · linarith only [h4674, h4759, hlam]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h4674, hlam, p4739_0]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h4721, hlam, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h4724, hlam, p4739_0]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [h4725, hlam, p4739_1]
                                    · have p4739_0 := h4739c.1
                                      have p4739_1 := h4739c.2.1
                                      have p4739_2 := h4739c.2.2.1
                                      have p4739_3 := h4739c.2.2.2
                                      linarith only [hlam, p4739_0]
                                  · linarith only [h1, h2, h4726, h4728, h4734, h4738, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1, h2, h4725, h4726, h4728, h4730, h4736, h4737, hc05, hc35, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h4675, h4724, h4730, h4736, hc03, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1, h2, h4724, h4726, h4730, h4733, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h1, h2, h4675, h4721, h4728, h4730, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h4675, h4721, h4725, hlam]
              · linarith only [h4675, h4721, h4724, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4774 | h4774
            · linarith only [h1, h2, h4774, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4776 | h4776
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4777 | h4777
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4778 | h4778
                  · linarith only [h0, h2, h4675, h4778, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4780 | h4780
                    · linarith only [h0, h4719, h4780, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4782 | h4782
                      · linarith only [h0, h4721, h4782, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4784 | h4784
                        · linarith only [h1, h2, h4774, h4780, h4784, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4786 | h4786
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4787 | h4787
                            · linarith only [h1, h2, h4784, h4786, h4787, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4789 | h4789
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4790 | h4790
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4791 | h4791
                                  · rcases h0bigk with h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c | h4792c
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [hlam, p4792_0]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h1, h2, h4786, h4791, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h2, hlam, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h0, hlam, p4792_0]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [hlam, p4792_0]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4675, hlam, p4792_0]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4719, hlam, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4721, hlam, p4792_0]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h1, hlam, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [hlam, p4792_0]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4774, hlam, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4674, h4675, h4782, h4787, hc12, hc34, hlam, hphi, ht23, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4719, h4787, hc01, hc34, hlam, hphi, ht12, ht23, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h0, h4719, h4787, hc12, hc34, hlam, hphi, ht23, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4719, h4787, hc03, hc34, hlam, hphi, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [hlam, p4792_0]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4674, h4719, h4782, h4787, hc12, hc34, hlam, hphi, ht23, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4674, hlam, p4792_0]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h0, h2, h4674, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4776, hlam, p4792_0]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [h4777, hlam, p4792_1]
                                    · have p4792_0 := h4792c.1
                                      have p4792_1 := h4792c.2.1
                                      have p4792_2 := h4792c.2.2.1
                                      have p4792_3 := h4792c.2.2.2
                                      linarith only [hlam, p4792_0]
                                  · linarith only [h1, h2, h4780, h4786, h4787, h4791, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h1, h2, h4776, h4777, h4780, h4786, h4790, hc03, hc35, hlam, hphi, ht0b, ht5b]
                              · linarith only [h1, h2, h4786, h4789, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h1, h2, h4776, h4784, h4786, hc13, hc34, hlam, hphi]
                · linarith only [h1, h2, h4776, h4777, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4823 | h4823
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4824 | h4824
                  · linarith only [h0, h4675, h4824, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4826 | h4826
                    · linarith only [h0, h4719, h4826, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4828 | h4828
                      · linarith only [h1, h4721, h4776, h4824, h4828, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4830 | h4830
                        · linarith only [h0, h1, h2, h4774, h4776, h4830, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4832 | h4832
                          · linarith only [h1, h4776, h4832, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4834 | h4834
                            · linarith only [h0, h2, h4830, h4834, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4836 | h4836
                              · linarith only [h0, h4675, h4776, h4834, h4836, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4838 | h4838
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4839 | h4839
                                  · rcases h0bigk with h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c | h4840c
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [hlam, p4840_0]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h0, h2, h4675, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h2, hlam, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h0, hlam, p4840_0]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [hlam, p4840_0]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h4675, hlam, p4840_0]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h4719, hlam, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h4721, hlam, p4840_0]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h1, hlam, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [hlam, p4840_0]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h4774, hlam, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h4776, hlam, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h4674, hc04, hc15, hlam, hphi, ht0b, ht5b, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h0, h4719, h4834, hc12, hc34, hlam, hphi, ht23, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h4719, h4834, hc03, hc34, hlam, hphi, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [hlam, p4840_0]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h1, h4719, h4776, h4824, h4834, hc12, hc34, hlam, hphi, ht23, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h4674, hlam, p4840_0]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h0, h2, h4674, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h1, h2, h4674, h4824, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [h4823, hlam, p4840_1]
                                    · have p4840_0 := h4840c.1
                                      have p4840_1 := h4840c.2.1
                                      have p4840_2 := h4840c.2.2.1
                                      have p4840_3 := h4840c.2.2.2
                                      linarith only [hlam, p4840_0]
                                  · linarith only [h2, h4674, h4823, h4826, h4834, h4839, hlam]
                                · linarith only [h2, h4674, h4823, h4826, h4838, hlam]
                · linarith only [h2, h4674, h4823, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4869 | h4869
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4870 | h4870
        · linarith only [h0, h2, h4870, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4872 | h4872
          · linarith only [h0, h4674, h4872, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4874 | h4874
            · linarith only [h1, h2, h4874, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4876 | h4876
              · linarith only [h0, h4674, h4869, h4876, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4878 | h4878
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4879 | h4879
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4880 | h4880
                    · linarith only [h0, h2, h4870, h4880, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4882 | h4882
                      · linarith only [h0, h4674, h4872, h4882, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4884 | h4884
                        · linarith only [h0, h4674, h4874, h4878, h4879, h4884, hlam]
                        · linarith only [h0, h2, h4879, h4884, hc23, hc34, hlam, hphi]
                  · linarith only [h4869, h4870, h4879, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4888 | h4888
                  · linarith only [h0, h2, h4878, h4888, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h4869, h4878, h4888, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4891 | h4891
        · linarith only [h1, h2, h4869, h4891, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4893 | h4893
          · linarith only [h1, h4674, h4869, h4893, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4895 | h4895
            · linarith only [h1, h2, h4895, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4897 | h4897
              · linarith only [h1, h4674, h4897, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4899 | h4899
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4900 | h4900
                  · linarith only [h0, h2, h4869, h4900, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4902 | h4902
                    · linarith only [h0, h4674, h4891, h4899, h4902, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4904 | h4904
                      · linarith only [h0, h2, h4893, h4902, h4904, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4906 | h4906
                        · linarith only [h1, h2, h4895, h4902, h4906, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4908 | h4908
                          · linarith only [h1, h4674, h4897, h4908, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4910 | h4910
                            · linarith only [h0, h2, h4906, h4910, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4912 | h4912
                              · linarith only [h1, h4674, h4900, h4908, h4912, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4914 | h4914
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4915 | h4915
                                  · rcases h0bigk with h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [hlam, p4916_0]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h0, h4674, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h0, h4674, h4869, h4904, hc12, hc25, hlam, hphi, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h2, hlam, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h4674, hlam, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h0, hlam, p4916_0]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [hlam, p4916_0]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h4869, hlam, p4916_0]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h4891, hlam, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h4893, hlam, p4916_0]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h1, hlam, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h0, h1, h4674, h4904, hc12, hc25, hlam, hphi, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [hlam, p4916_0]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h4895, hlam, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h4897, hlam, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h2, h4902, h4910, hc01, hc34, hlam, hphi, ht12, ht23, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h0, h2, h4902, h4910, hc12, hc34, hlam, hphi, ht23, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h2, h4902, h4910, hc03, hc34, hlam, hphi, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [hlam, p4916_0]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h1, h2, h4674, h4900, h4902, h4910, hc12, hc34, hlam, hphi, ht23, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h1, h4900, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h0, h4674, h4904, hc12, hc25, hlam, hphi, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h1, h4897, h4900, h4915, hc12, hc34, hlam, hphi, ht23, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [h4899, hlam, p4916_1]
                                    · have p4916_0 := h4916c.1
                                      have p4916_1 := h4916c.2.1
                                      have p4916_2 := h4916c.2.2.1
                                      have p4916_3 := h4916c.2.2.2
                                      linarith only [hlam, p4916_0]
                                  · linarith only [h2, h4899, h4902, h4910, h4915, hlam]
                                · linarith only [h2, h4899, h4902, h4914, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4944 | h4944
                  · linarith only [h0, h2, h4899, h4944, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4946 | h4946
                    · linarith only [h0, h2, h4899, h4946, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4948 | h4948
                      · linarith only [h0, h4893, h4948, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4950 | h4950
                        · linarith only [h1, h2, h4899, h4950, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4952 | h4952
                          · linarith only [h1, h2, h4869, h4897, h4899, h4952, hc02, hc45, hlam, hphi, ht23, ht34]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4954 | h4954
                            · linarith only [h0, h2, h4950, h4954, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4956 | h4956
                              · linarith only [h1, h4674, h4944, h4952, h4954, h4956, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4958 | h4958
                                · linarith only [h1, h2, h4899, h4944, h4958, hc12, hc24, hlam, hphi]
                                · linarith only [h1, h2, h4944, h4946, h4958, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
