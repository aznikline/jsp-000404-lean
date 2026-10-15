import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13744000 in
set_option maxHeartbeats 13744000 in
theorem r1l7_13_24_L_I_H_I_s9_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h8811 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h8812 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h8813 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  rcases m.htr 0 2 4 (by decide) (by decide) with h8814 | h8814
  · rcases m.htr 0 3 4 (by decide) (by decide) with h8815 | h8815
    · rcases m.htr 0 3 5 (by decide) (by decide) with h8816 | h8816
      · rcases m.htr 0 4 5 (by decide) (by decide) with h8817 | h8817
        · rcases m.htr 1 2 3 (by decide) (by decide) with h8818 | h8818
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8819 | h8819
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8820 | h8820
              · rcases m.htr 1 3 5 (by decide) (by decide) with h8821 | h8821
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8822 | h8822
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8823 | h8823
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8824 | h8824
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8825 | h8825
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8826 | h8826
                          · rcases h3bigk with h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c | h8827c
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h7360, hlam, p8827_1]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8823, h8826, hc03, hc45, hlam, hphi, ht0b, ht5b, p8827_1]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              rcases p8827_3 (m.d 0 3) (by simp) with h8831 | h8831
                              · rcases p8827_3 (m.d 1 3) (by simp) with h8832 | h8832
                                · rcases p8827_3 (m.d 2 3) (by simp) with h8833 | h8833
                                  · linarith only [h8813, h8833, hlam]
                                  · linarith only [h8823, h8833, hlam]
                                · linarith only [h8820, h8832, hlam]
                              · linarith only [h8831, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              rcases p8827_3 (m.d 0 3) (by simp) with h8838 | h8838
                              · rcases p8827_3 (m.d 1 3) (by simp) with h8839 | h8839
                                · rcases p8827_3 (m.d 2 3) (by simp) with h8840 | h8840
                                  · linarith only [h8813, h8840, hlam]
                                  · linarith only [h8824, h8840, hlam]
                                · linarith only [h8821, h8839, hlam]
                              · linarith only [h8838, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h7360, h8811, h8818, h8819, h8823, h8826, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8827_1]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8818, h8823, h8826, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8827_1]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              rcases p8827_3 (m.d 0 3) (by simp) with h8848 | h8848
                              · linarith only [h7360, h8848, hlam]
                              · linarith only [h8815, h8848, hlam]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              rcases p8827_3 (m.d 0 3) (by simp) with h8851 | h8851
                              · linarith only [h7360, h8851, hlam]
                              · linarith only [h8816, h8851, hlam]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8813, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8818, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h0, h8813, h8826, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8827_1]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              rcases p8827_3 (m.d 0 3) (by simp) with h8858 | h8858
                              · rcases p8827_3 (m.d 1 3) (by simp) with h8859 | h8859
                                · rcases p8827_3 (m.d 2 3) (by simp) with h8860 | h8860
                                  · rcases p8827_3 (m.d 3 4) (by simp) with h8861 | h8861
                                    · linarith only [h8823, h8861, hlam]
                                    · linarith only [h8826, h8861, hlam]
                                  · linarith only [h8860, hlam, p8827_0]
                                · linarith only [h8821, h8859, hlam]
                              · linarith only [h8816, h8858, hlam]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8815, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8820, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8823, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h0, h8811, h8819, h8823, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8827_1]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8816, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8821, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8824, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [h8826, hlam, p8827_0]
                            · have p8827_0 := h8827c.1
                              have p8827_1 := h8827c.2.1
                              have p8827_2 := h8827c.2.2.1
                              have p8827_3 := h8827c.2.2.2
                              linarith only [hlam, p8827_0]
                          · linarith only [h7360, h8811, h8818, h8822, h8826, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h7360, h8811, h8818, h8822, h8825, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h7360, h8811, h8818, h8821, h8822, h8823, h8824, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8880 | h8880
                      · linarith only [h7360, h8811, h8818, h8820, h8823, h8880, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8882 | h8882
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8883 | h8883
                          · rcases h3bigk with h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h7360, hlam, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              rcases p8884_3 (m.d 0 3) (by simp) with h8887 | h8887
                              · rcases p8884_3 (m.d 1 3) (by simp) with h8888 | h8888
                                · rcases p8884_3 (m.d 2 3) (by simp) with h8889 | h8889
                                  · linarith only [h8813, h8889, hlam]
                                  · rcases p8884_3 (m.d 3 4) (by simp) with h8891 | h8891
                                    · linarith only [h8815, h8891, hlam]
                                    · linarith only [h8823, h8891, hlam]
                                · linarith only [h8818, h8888, hlam]
                              · linarith only [h8813, h8887, hlam]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              rcases p8884_3 (m.d 0 3) (by simp) with h8896 | h8896
                              · rcases p8884_3 (m.d 1 3) (by simp) with h8897 | h8897
                                · rcases p8884_3 (m.d 2 3) (by simp) with h8898 | h8898
                                  · linarith only [h8813, h8898, hlam]
                                  · rcases p8884_3 (m.d 3 4) (by simp) with h8900 | h8900
                                    · linarith only [h8900, hlam, p8884_0]
                                    · rcases p8884_3 (m.d 3 5) (by simp) with h8902 | h8902
                                      · linarith only [h8816, h8902, hlam]
                                      · rcases h4bigk with h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c | h8904c
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [hlam, p8904_0]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h7360, h8811, h8818, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h7360, h8811, h8818, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h7360, h8811, h8818, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h7360, h8811, h8818, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8811, hlam, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [hlam, p8904_0]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8882, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h7360, h8811, h8818, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h7360, h8811, h8818, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8814, hlam, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8819, hlam, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [hlam, p8904_0]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8823, hlam, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h0, h8814, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8815, hlam, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8820, hlam, p8904_0]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p8884_1, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [hlam, p8904_0]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h7360, h8818, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8884_1, p8904_1]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8817, hlam, p8904_0]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8822, hlam, p8904_0]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8882, hlam, p8904_0]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [h8883, hlam, p8904_0]
                                        · have p8904_0 := h8904c.1
                                          have p8904_1 := h8904c.2.1
                                          have p8904_2 := h8904c.2.2.1
                                          have p8904_3 := h8904c.2.2.2
                                          linarith only [hlam, p8904_0]
                                · linarith only [h8820, h8897, hlam]
                              · linarith only [h8896, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              rcases p8884_3 (m.d 0 3) (by simp) with h8932 | h8932
                              · rcases p8884_3 (m.d 1 3) (by simp) with h8933 | h8933
                                · rcases p8884_3 (m.d 2 3) (by simp) with h8934 | h8934
                                  · linarith only [h8813, h8934, hlam]
                                  · rcases p8884_3 (m.d 3 4) (by simp) with h8936 | h8936
                                    · linarith only [h8815, h8936, hlam]
                                    · linarith only [h8883, h8936, hlam]
                                · linarith only [h8821, h8933, hlam]
                              · linarith only [h8932, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h7360, h8812, h8818, h8821, h8880, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h7360, h8812, h8821, h8880, hlam, p8884_2]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              rcases p8884_3 (m.d 0 3) (by simp) with h8944 | h8944
                              · linarith only [h7360, h8944, hlam]
                              · linarith only [h8815, h8944, hlam]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              rcases p8884_3 (m.d 0 3) (by simp) with h8947 | h8947
                              · linarith only [h7360, h8947, hlam]
                              · linarith only [h8816, h8947, hlam]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8813, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8818, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8823, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8880, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8815, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8820, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h7360, h8811, h8820, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h7360, h8811, h8818, h8820, h8880, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8816, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8821, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h7360, h8812, h8818, h8821, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8883, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [hlam, p8884_0]
                          · linarith only [h7360, h8811, h8818, h8819, h8882, h8883, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h7360, h8811, h8818, h8822, h8882, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8967 | h8967
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8968 | h8968
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8969 | h8969
                        · linarith only [h8819, h8822, h8969, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8971 | h8971
                          · linarith only [h8819, h8822, h8967, h8971, hlam]
                          · rcases h3bigk with h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c | h8973c
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h7360, hlam, p8973_1]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              rcases p8973_3 (m.d 0 3) (by simp) with h8976 | h8976
                              · rcases p8973_3 (m.d 1 3) (by simp) with h8977 | h8977
                                · rcases p8973_3 (m.d 2 3) (by simp) with h8978 | h8978
                                  · linarith only [h8813, h8978, hlam]
                                  · rcases p8973_3 (m.d 3 4) (by simp) with h8980 | h8980
                                    · linarith only [h8815, h8980, hlam]
                                    · rcases p8973_3 (m.d 3 5) (by simp) with h8982 | h8982
                                      · linarith only [h8816, h8982, hlam]
                                      · rcases h4bigk with h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c | h8984c
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [hlam, p8984_0]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h7360, h8811, h8818, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h7360, h8811, h8818, h8967, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h7360, h8811, h8818, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h7360, h8811, h8818, h8822, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h8811, hlam, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [hlam, p8984_0]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h7360, h8811, h8818, h8967, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h7360, h8811, h8818, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h8822, hlam, p8984_0]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h8814, hlam, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h8819, hlam, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [hlam, p8984_0]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h0, h8814, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h8969, hlam, p8984_0]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h8815, hlam, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h8820, hlam, p8984_0]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h8967, hlam, p8984_0]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [hlam, p8984_0]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h8971, hlam, p8984_0]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h8817, hlam, p8984_0]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [hc14, hc45, hlam, hphi, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h7360, h8811, h8817, h8818, h8967, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [h7360, h8811, h8817, h8818, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8984_1]
                                        · have p8984_0 := h8984c.1
                                          have p8984_1 := h8984c.2.1
                                          have p8984_2 := h8984c.2.2.1
                                          have p8984_3 := h8984c.2.2.2
                                          linarith only [hlam, p8984_0]
                                · linarith only [h8818, h8977, hlam]
                              · linarith only [h8813, h8976, hlam]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              rcases p8973_3 (m.d 0 3) (by simp) with h9012 | h9012
                              · rcases p8973_3 (m.d 1 3) (by simp) with h9013 | h9013
                                · rcases p8973_3 (m.d 2 3) (by simp) with h9014 | h9014
                                  · linarith only [h8813, h9014, hlam]
                                  · linarith only [h8967, h9014, hlam]
                                · linarith only [h8820, h9013, hlam]
                              · linarith only [h9012, hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              rcases p8973_3 (m.d 0 3) (by simp) with h9019 | h9019
                              · rcases p8973_3 (m.d 1 3) (by simp) with h9020 | h9020
                                · rcases p8973_3 (m.d 2 3) (by simp) with h9021 | h9021
                                  · linarith only [h8813, h9021, hlam]
                                  · linarith only [h8968, h9021, hlam]
                                · linarith only [h8821, h9020, hlam]
                              · linarith only [h9019, hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h7360, h8811, h8817, h8818, h8819, h8822, h8967, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8973_1]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              rcases p8973_3 (m.d 0 3) (by simp) with h9028 | h9028
                              · linarith only [h7360, h9028, hlam]
                              · linarith only [h8813, h9028, hlam]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h7360, h8811, h8817, h8819, h8822, h8967, hlam, p8973_2]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              rcases p8973_3 (m.d 0 3) (by simp) with h9032 | h9032
                              · linarith only [h7360, h9032, hlam]
                              · linarith only [h8816, h9032, hlam]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h8813, hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h8818, hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              rcases p8973_3 (m.d 0 3) (by simp) with h9038 | h9038
                              · rcases p8973_3 (m.d 1 3) (by simp) with h9039 | h9039
                                · rcases p8973_3 (m.d 2 3) (by simp) with h9040 | h9040
                                  · rcases p8973_3 (m.d 3 4) (by simp) with h9041 | h9041
                                    · linarith only [h9041, hlam, p8973_0]
                                    · rcases p8973_3 (m.d 3 5) (by simp) with h9043 | h9043
                                      · linarith only [h8968, h9043, hlam]
                                      · linarith only [h8971, h9043, hlam]
                                  · linarith only [h9040, hlam, p8973_0]
                                · linarith only [h8820, h9039, hlam]
                              · linarith only [h8815, h9038, hlam]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              rcases p8973_3 (m.d 0 3) (by simp) with h9049 | h9049
                              · rcases p8973_3 (m.d 1 3) (by simp) with h9050 | h9050
                                · rcases p8973_3 (m.d 2 3) (by simp) with h9051 | h9051
                                  · rcases p8973_3 (m.d 3 4) (by simp) with h9052 | h9052
                                    · linarith only [h8967, h9052, hlam]
                                    · rcases p8973_3 (m.d 3 5) (by simp) with h9054 | h9054
                                      · linarith only [h9054, hlam, p8973_0]
                                      · rcases h4bigk with h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c | h9056c
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [hlam, p9056_0]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h7360, h8811, h8819, h8967, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h7360, h8811, h8967, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h7360, h8811, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h7360, h8811, h8819, h8822, h8967, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8811, hlam, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [hlam, p9056_0]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8822, h8967, hc34, hc45, hlam, hphi, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h7360, h8811, h8818, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8822, hlam, p9056_0]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8814, hlam, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8819, hlam, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [hlam, p9056_0]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h0, h8814, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8969, hlam, p9056_0]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8815, hlam, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8820, hlam, p9056_0]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8967, hlam, p9056_0]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [hlam, p9056_0]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8971, hlam, p9056_0]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h8817, hlam, p9056_0]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h7360, h8811, h8817, h8818, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h7360, h8811, h8817, h8818, h8967, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [h7360, h8811, h8817, h8818, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9056_1]
                                        · have p9056_0 := h9056c.1
                                          have p9056_1 := h9056c.2.1
                                          have p9056_2 := h9056c.2.2.1
                                          have p9056_3 := h9056c.2.2.2
                                          linarith only [hlam, p9056_0]
                                  · linarith only [h9051, hlam, p8973_0]
                                · linarith only [h8821, h9050, hlam]
                              · linarith only [h8816, h9049, hlam]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h8815, hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h8820, hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h8967, hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h8971, hlam, p8973_1]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h8816, hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h8821, hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h8968, hlam, p8973_0]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [h7360, h8812, h8818, h8821, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8973_1]
                            · have p8973_0 := h8973c.1
                              have p8973_1 := h8973c.2.1
                              have p8973_2 := h8973c.2.2.1
                              have p8973_3 := h8973c.2.2.2
                              linarith only [hlam, p8973_0]
                      · linarith only [h7360, h8811, h8817, h8818, h8821, h8822, h8967, h8968, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h7360, h8811, h8817, h8818, h8820, h8822, h8967, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h7360, h8811, h8816, h8821, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h7360, h8815, h8820, hlam]
            · linarith only [h0, h8814, h8819, hlam]
          · linarith only [h0, h8813, h8818, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9101 | h9101
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9102 | h9102
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9103 | h9103
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9104 | h9104
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9105 | h9105
                  · linarith only [h8811, h8817, h9105, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9107 | h9107
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9108 | h9108
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9109 | h9109
                        · linarith only [h8811, h8817, h9102, h9109, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9111 | h9111
                          · linarith only [h8811, h8817, h9102, h9107, h9111, hlam]
                          · rcases h3bigk with h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h7360, hlam, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 3) (by simp) with h9116 | h9116
                              · rcases p9113_3 (m.d 1 3) (by simp) with h9117 | h9117
                                · rcases p9113_3 (m.d 2 3) (by simp) with h9118 | h9118
                                  · linarith only [h8813, h9118, hlam]
                                  · rcases p9113_3 (m.d 3 4) (by simp) with h9120 | h9120
                                    · linarith only [h8815, h9120, hlam]
                                    · rcases p9113_3 (m.d 3 5) (by simp) with h9122 | h9122
                                      · linarith only [h8816, h9122, hlam]
                                      · rcases h4bigk with h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [hlam, p9124_0]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h8817, hc14, hc45, hlam, hphi, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h8817, h9107, hc34, hc45, hlam, hphi, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h8817, hc34, hc45, hlam, hphi, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h8817, hlam, p9124_0]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h8811, hlam, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [hlam, p9124_0]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h8811, h9107, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h7360, h8812, h9101, h9105, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h9105, hlam, p9124_0]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h8814, hlam, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h9102, hlam, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [hlam, p9124_0]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h8814, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h9109, hlam, p9124_0]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h8815, hlam, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h9103, hlam, p9124_0]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h9107, hlam, p9124_0]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [hlam, p9124_0]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h9111, hlam, p9124_0]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [hc04, hc45, hlam, hphi, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [hc14, hc45, hlam, hphi, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [h9107, hc34, hc45, hlam, hphi, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [hc34, hc45, hlam, hphi, p9124_1]
                                        · have p9124_0 := h9124c.1
                                          have p9124_1 := h9124c.2.1
                                          have p9124_2 := h9124c.2.2.1
                                          have p9124_3 := h9124c.2.2.2
                                          linarith only [hlam, p9124_0]
                                · linarith only [h9101, h9117, hlam]
                              · linarith only [h8813, h9116, hlam]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 3) (by simp) with h9152 | h9152
                              · rcases p9113_3 (m.d 1 3) (by simp) with h9153 | h9153
                                · rcases p9113_3 (m.d 2 3) (by simp) with h9154 | h9154
                                  · linarith only [h8813, h9154, hlam]
                                  · linarith only [h9107, h9154, hlam]
                                · linarith only [h9103, h9153, hlam]
                              · linarith only [h9152, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 3) (by simp) with h9159 | h9159
                              · rcases p9113_3 (m.d 1 3) (by simp) with h9160 | h9160
                                · rcases p9113_3 (m.d 2 3) (by simp) with h9161 | h9161
                                  · linarith only [h8813, h9161, hlam]
                                  · linarith only [h9108, h9161, hlam]
                                · linarith only [h9104, h9160, hlam]
                              · linarith only [h9159, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 3) (by simp) with h9166 | h9166
                              · linarith only [h7360, h9166, hlam]
                              · rcases p9113_3 (m.d 1 3) (by simp) with h9168 | h9168
                                · rcases p9113_3 (m.d 2 3) (by simp) with h9169 | h9169
                                  · linarith only [h9101, h9169, hlam]
                                  · rcases p9113_3 (m.d 3 4) (by simp) with h9171 | h9171
                                    · linarith only [h9103, h9171, hlam]
                                    · rcases p9113_3 (m.d 3 5) (by simp) with h9173 | h9173
                                      · linarith only [h9104, h9173, hlam]
                                      · rcases h4bigk with h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c | h9175c
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [hlam, p9175_0]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h7360, h8812, h8817, h9101, h9102, h9107, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9113_1, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h7360, h8812, h8817, h9101, h9107, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9113_1, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h7360, h8812, h8817, h9101, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9113_1, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h8817, hlam, p9175_0]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h8811, hlam, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [hlam, p9175_0]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h7360, h8811, h9101, h9107, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9113_1, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h7360, h8811, h9101, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9113_1, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h9105, hlam, p9175_0]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h8814, hlam, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h9102, hlam, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [hlam, p9175_0]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h0, h8814, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h9109, hlam, p9175_0]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h8815, hlam, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h9103, hlam, p9175_0]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h9107, hlam, p9175_0]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [hlam, p9175_0]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h9111, hlam, p9175_0]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [hc04, hc45, hlam, hphi, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h9102, hc24, hc45, hlam, hphi, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [h9107, hc34, hc45, hlam, hphi, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [hc34, hc45, hlam, hphi, p9175_1]
                                        · have p9175_0 := h9175c.1
                                          have p9175_1 := h9175c.2.1
                                          have p9175_2 := h9175c.2.2.1
                                          have p9175_3 := h9175c.2.2.2
                                          linarith only [hlam, p9175_0]
                                · linarith only [h7360, h9168, hlam]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 3) (by simp) with h9203 | h9203
                              · linarith only [h7360, h9203, hlam]
                              · linarith only [h8813, h9203, hlam]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 3) (by simp) with h9206 | h9206
                              · linarith only [h7360, h9206, hlam]
                              · linarith only [h8815, h9206, hlam]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 3) (by simp) with h9209 | h9209
                              · linarith only [h7360, h9209, hlam]
                              · linarith only [h8816, h9209, hlam]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8813, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h9101, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 3) (by simp) with h9215 | h9215
                              · rcases p9113_3 (m.d 1 3) (by simp) with h9216 | h9216
                                · rcases p9113_3 (m.d 2 3) (by simp) with h9217 | h9217
                                  · rcases p9113_3 (m.d 3 4) (by simp) with h9218 | h9218
                                    · linarith only [h9218, hlam, p9113_0]
                                    · rcases p9113_3 (m.d 3 5) (by simp) with h9220 | h9220
                                      · linarith only [h9108, h9220, hlam]
                                      · linarith only [h9111, h9220, hlam]
                                  · linarith only [h9217, hlam, p9113_0]
                                · linarith only [h9103, h9216, hlam]
                              · linarith only [h8815, h9215, hlam]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 3) (by simp) with h9226 | h9226
                              · rcases p9113_3 (m.d 1 3) (by simp) with h9227 | h9227
                                · rcases p9113_3 (m.d 2 3) (by simp) with h9228 | h9228
                                  · rcases p9113_3 (m.d 3 4) (by simp) with h9229 | h9229
                                    · linarith only [h9107, h9229, hlam]
                                    · rcases p9113_3 (m.d 3 5) (by simp) with h9231 | h9231
                                      · linarith only [h9231, hlam, p9113_0]
                                      · rcases h4bigk with h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c | h9233c
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [hlam, p9233_0]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h0, h8811, h9102, h9107, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h0, h8811, h9107, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h0, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h8817, hlam, p9233_0]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h8811, hlam, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [hlam, p9233_0]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h0, h8811, h9107, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h7360, h8812, h9101, h9105, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h9105, hlam, p9233_0]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h8814, hlam, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h9102, hlam, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [hlam, p9233_0]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h0, h8814, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h9109, hlam, p9233_0]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h8815, hlam, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h9103, hlam, p9233_0]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h9107, hlam, p9233_0]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [hlam, p9233_0]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h9111, hlam, p9233_0]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [hc04, hc45, hlam, hphi, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [hc14, hc45, hlam, hphi, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [h9107, hc34, hc45, hlam, hphi, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [hc34, hc45, hlam, hphi, p9233_1]
                                        · have p9233_0 := h9233c.1
                                          have p9233_1 := h9233c.2.1
                                          have p9233_2 := h9233c.2.2.1
                                          have p9233_3 := h9233c.2.2.2
                                          linarith only [hlam, p9233_0]
                                  · linarith only [h9228, hlam, p9113_0]
                                · linarith only [h9104, h9227, hlam]
                              · linarith only [h8816, h9226, hlam]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8815, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h9103, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h9107, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h9111, hlam, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8816, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h9104, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h9108, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h7360, h8812, h9101, h9104, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [hlam, p9113_0]
                      · linarith only [h7360, h8812, h9101, h9104, h9107, h9108, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9273 | h9273
                      · linarith only [h7360, h8811, h9101, h9103, h9107, h9273, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9275 | h9275
                        · linarith only [h8811, h8817, h9103, h9107, h9275, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9277 | h9277
                          · linarith only [h8811, h8817, h9103, h9277, hlam]
                          · rcases h3bigk with h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c | h9279c
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h7360, hlam, p9279_1]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              rcases p9279_3 (m.d 0 3) (by simp) with h9282 | h9282
                              · rcases p9279_3 (m.d 1 3) (by simp) with h9283 | h9283
                                · rcases p9279_3 (m.d 2 3) (by simp) with h9284 | h9284
                                  · linarith only [h8813, h9284, hlam]
                                  · rcases p9279_3 (m.d 3 4) (by simp) with h9286 | h9286
                                    · linarith only [h8815, h9286, hlam]
                                    · linarith only [h9107, h9286, hlam]
                                · linarith only [h9101, h9283, hlam]
                              · linarith only [h8813, h9282, hlam]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              rcases p9279_3 (m.d 0 3) (by simp) with h9291 | h9291
                              · rcases p9279_3 (m.d 1 3) (by simp) with h9292 | h9292
                                · rcases p9279_3 (m.d 2 3) (by simp) with h9293 | h9293
                                  · linarith only [h8813, h9293, hlam]
                                  · rcases p9279_3 (m.d 3 4) (by simp) with h9295 | h9295
                                    · linarith only [h9295, hlam, p9279_0]
                                    · rcases p9279_3 (m.d 3 5) (by simp) with h9297 | h9297
                                      · linarith only [h8816, h9297, hlam]
                                      · linarith only [h9277, h9297, hlam]
                                · linarith only [h9103, h9292, hlam]
                              · linarith only [h9291, hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              rcases p9279_3 (m.d 0 3) (by simp) with h9302 | h9302
                              · rcases p9279_3 (m.d 1 3) (by simp) with h9303 | h9303
                                · rcases p9279_3 (m.d 2 3) (by simp) with h9304 | h9304
                                  · linarith only [h8813, h9304, hlam]
                                  · rcases p9279_3 (m.d 3 4) (by simp) with h9306 | h9306
                                    · linarith only [h8815, h9306, hlam]
                                    · rcases p9279_3 (m.d 3 5) (by simp) with h9308 | h9308
                                      · linarith only [h9308, hlam, p9279_0]
                                      · rcases h4bigk with h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [hlam, p9310_0]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h9103, h9107, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h8817, hc24, hc45, hlam, hphi, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h8817, h9107, hc23, hc45, hlam, hphi, ht34, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h8817, hlam, p9310_0]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h8811, hlam, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [hlam, p9310_0]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h7360, h8812, h9101, h9105, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h7360, h8812, h9101, h9105, h9107, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h9105, hlam, p9310_0]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h8814, hlam, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h9102, hlam, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [hlam, p9310_0]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h9107, hlam, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h9275, hlam, p9310_0]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h8815, hlam, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h9103, hlam, p9310_0]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h8815, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [hlam, p9310_0]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h9277, hlam, p9310_0]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [hc04, hc45, hlam, hphi, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h9102, hc24, hc45, hlam, hphi, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h9107, hc23, hc45, hlam, hphi, ht34, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [h9107, hc23, hc45, hlam, hphi, ht34, p9310_1]
                                        · have p9310_0 := h9310c.1
                                          have p9310_1 := h9310c.2.1
                                          have p9310_2 := h9310c.2.2.1
                                          have p9310_3 := h9310c.2.2.2
                                          linarith only [hlam, p9310_0]
                                · linarith only [h9104, h9303, hlam]
                              · linarith only [h9302, hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h7360, h8811, h9101, h9103, h9107, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9279_1]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h7360, h8811, h9103, h9107, hlam, p9279_2]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              rcases p9279_3 (m.d 0 3) (by simp) with h9341 | h9341
                              · linarith only [h7360, h9341, hlam]
                              · linarith only [h8815, h9341, hlam]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              rcases p9279_3 (m.d 0 3) (by simp) with h9344 | h9344
                              · linarith only [h7360, h9344, hlam]
                              · linarith only [h8816, h9344, hlam]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h8813, hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h9101, hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h9107, hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h9273, hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h8815, hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h9103, hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h7360, h8812, h9103, h9105, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9279_1]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h9277, hlam, p9279_1]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h8816, hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h9104, hlam, p9279_0]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h7360, h8812, h9101, h9104, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9279_1]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [h7360, h8812, h9101, h9104, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9279_1]
                            · have p9279_0 := h9279c.1
                              have p9279_1 := h9279c.2.1
                              have p9279_2 := h9279c.2.2.1
                              have p9279_3 := h9279c.2.2.2
                              linarith only [hlam, p9279_0]
                · linarith only [h7360, h8812, h8816, h9104, hc03, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h7360, h8815, h9103, hlam]
            · linarith only [h0, h8814, h9102, hlam]
          · linarith only [h0, h8813, h9101, hlam]
      · linarith only [h7360, h8812, h8816, hlam]
    · linarith only [h7360, h8811, h8815, hlam]
  · linarith only [h0, h8811, h8814, hlam]

end R2N4
