import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10168000 in
set_option maxHeartbeats 10168000 in
theorem r1l7_11_23_L_I_H_I_s13_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h13812 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h13813 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  rcases m.htr 0 2 4 (by decide) (by decide) with h13814 | h13814
  · rcases m.htr 0 3 4 (by decide) (by decide) with h13815 | h13815
    · rcases m.htr 0 3 5 (by decide) (by decide) with h13816 | h13816
      · rcases m.htr 0 4 5 (by decide) (by decide) with h13817 | h13817
        · rcases m.htr 1 2 3 (by decide) (by decide) with h13818 | h13818
          · rcases m.htr 1 2 4 (by decide) (by decide) with h13819 | h13819
            · rcases m.htr 1 2 5 (by decide) (by decide) with h13820 | h13820
              · rcases m.htr 1 3 4 (by decide) (by decide) with h13821 | h13821
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13822 | h13822
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h13823 | h13823
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13824 | h13824
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h13825 | h13825
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h13826 | h13826
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13827 | h13827
                            · rcases h1bigk with h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c | h13828c
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h0, hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h11385, hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h12794, hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                rcases p13828_3 (m.d 0 1) (by simp) with h13833 | h13833
                                · rcases p13828_3 (m.d 1 2) (by simp) with h13834 | h13834
                                  · rcases p13828_3 (m.d 1 3) (by simp) with h13835 | h13835
                                    · rcases p13828_3 (m.d 1 4) (by simp) with h13836 | h13836
                                      · rcases p13828_3 (m.d 1 5) (by simp) with h13837 | h13837
                                        · linarith only [h13837, hlam, p13828_0]
                                        · rcases h3bigk with h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h11385, hlam, p13839_1]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13824, h13827, hc03, hc45, hlam, hphi, ht0b, ht5b, p13839_1]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13813, h13827, hc02, hc45, hlam, hphi, ht0b, ht5b, p13839_1]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            rcases p13839_3 (m.d 0 3) (by simp) with h13844 | h13844
                                            · rcases p13839_3 (m.d 1 3) (by simp) with h13845 | h13845
                                              · rcases p13839_3 (m.d 2 3) (by simp) with h13846 | h13846
                                                · linarith only [h13813, h13846, hlam]
                                                · linarith only [h13825, h13846, hlam]
                                              · linarith only [h13822, h13845, hlam]
                                            · linarith only [h13844, hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h11385, h13818, h13820, h13825, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13828_1, p13839_1]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13818, h13824, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13839_1]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13818, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13839_1]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            rcases p13839_3 (m.d 0 3) (by simp) with h13855 | h13855
                                            · linarith only [h11385, h13855, hlam]
                                            · linarith only [h13816, h13855, hlam]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13813, hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13818, hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13827, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13839_1]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h0, h13813, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13839_1]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13815, hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13821, hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13824, hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13815, h13827, hc03, hc45, hlam, hphi, ht0b, ht5b, p13839_1]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13816, hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13822, hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13825, hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [h13827, hlam, p13839_0]
                                          · have p13839_0 := h13839c.1
                                            have p13839_1 := h13839c.2.1
                                            have p13839_2 := h13839c.2.2.1
                                            have p13839_3 := h13839c.2.2.2
                                            linarith only [hlam, p13839_0]
                                      · linarith only [h13823, h13836, hlam]
                                    · linarith only [h13822, h13835, hlam]
                                  · linarith only [h13820, h13834, hlam]
                                · linarith only [h13833, hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                rcases p13828_3 (m.d 0 1) (by simp) with h13877 | h13877
                                · linarith only [h13877, hlam, p13828_0]
                                · rcases p13828_3 (m.d 1 2) (by simp) with h13879 | h13879
                                  · rcases p13828_3 (m.d 1 3) (by simp) with h13880 | h13880
                                    · linarith only [h13818, h13880, hlam]
                                    · linarith only [h11385, h13880, hlam]
                                  · linarith only [h13879, hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h11385, hc01, hc12, hlam, hphi, p13828_1]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h12794, h13812, h13820, h13825, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13828_1]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                rcases p13828_3 (m.d 0 1) (by simp) with h13887 | h13887
                                · linarith only [h0, h13887, hlam]
                                · linarith only [h13812, h13887, hlam]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                rcases p13828_3 (m.d 0 1) (by simp) with h13890 | h13890
                                · linarith only [h13890, hlam, p13828_0]
                                · rcases p13828_3 (m.d 1 2) (by simp) with h13892 | h13892
                                  · rcases p13828_3 (m.d 1 3) (by simp) with h13893 | h13893
                                    · rcases p13828_3 (m.d 1 4) (by simp) with h13894 | h13894
                                      · linarith only [h13821, h13894, hlam]
                                      · linarith only [h12794, h13894, hlam]
                                    · linarith only [h13893, hlam, p13828_0]
                                  · linarith only [h0, h13892, hlam]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h13818, hlam, p13828_1]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h12794, h13812, h13818, h13820, h13825, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13828_1]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                rcases p13828_3 (m.d 0 1) (by simp) with h13902 | h13902
                                · linarith only [h11385, h13902, hlam]
                                · linarith only [h13812, h13902, hlam]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                rcases p13828_3 (m.d 0 1) (by simp) with h13905 | h13905
                                · linarith only [h13905, hlam, p13828_0]
                                · rcases p13828_3 (m.d 1 2) (by simp) with h13907 | h13907
                                  · rcases p13828_3 (m.d 1 3) (by simp) with h13908 | h13908
                                    · rcases p13828_3 (m.d 1 4) (by simp) with h13909 | h13909
                                      · rcases p13828_3 (m.d 1 5) (by simp) with h13910 | h13910
                                        · linarith only [h13823, h13910, hlam]
                                        · rcases h3bigk with h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c | h13912c
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h11385, hlam, p13912_1]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h11385, h13824, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13912_1]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h0, h13813, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13912_1]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            rcases p13912_3 (m.d 0 3) (by simp) with h13917 | h13917
                                            · rcases p13912_3 (m.d 1 3) (by simp) with h13918 | h13918
                                              · rcases p13912_3 (m.d 2 3) (by simp) with h13919 | h13919
                                                · linarith only [h13813, h13919, hlam]
                                                · linarith only [h13825, h13919, hlam]
                                              · linarith only [h13822, h13918, hlam]
                                            · linarith only [h13917, hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h11385, h13812, h13818, h13820, h13825, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13912_1]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13818, h13824, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13912_1]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13818, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13912_1]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            rcases p13912_3 (m.d 0 3) (by simp) with h13928 | h13928
                                            · linarith only [h11385, h13928, hlam]
                                            · linarith only [h13816, h13928, hlam]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13813, hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13818, hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13827, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13912_1]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h0, h13813, h13827, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13912_1]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13815, hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13821, hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13824, hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13815, h13827, hc03, hc45, hlam, hphi, ht0b, ht5b, p13912_1]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13816, hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13822, hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13825, hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [h13827, hlam, p13912_0]
                                          · have p13912_0 := h13912c.1
                                            have p13912_1 := h13912c.2.1
                                            have p13912_2 := h13912c.2.2.1
                                            have p13912_3 := h13912c.2.2.2
                                            linarith only [hlam, p13912_0]
                                      · linarith only [h13909, hlam, p13828_0]
                                    · linarith only [h11385, h13908, hlam]
                                  · linarith only [h0, h13907, hlam]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h13819, hlam, p13828_1]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h13821, hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                rcases p13828_3 (m.d 0 1) (by simp) with h13952 | h13952
                                · linarith only [h12794, h13952, hlam]
                                · linarith only [h13812, h13952, hlam]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h13812, hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h13820, hlam, p13828_1]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h13822, hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [h13823, hlam, p13828_0]
                              · have p13828_0 := h13828c.1
                                have p13828_1 := h13828c.2.1
                                have p13828_2 := h13828c.2.2.1
                                have p13828_3 := h13828c.2.2.2
                                linarith only [hlam, p13828_0]
                            · rcases h1bigk with h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c | h13960c
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h0, hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h11385, hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h12794, hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h0, h13820, h13826, h13827, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13960_1]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h13812, h13820, h13826, h13827, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13960_1]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h11385, hc01, hc12, hlam, hphi, p13960_1]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h12794, h13812, h13820, h13826, h13827, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13960_1]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                rcases p13960_3 (m.d 0 1) (by simp) with h13970 | h13970
                                · linarith only [h0, h13970, hlam]
                                · linarith only [h13812, h13970, hlam]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h13812, h13820, h13826, h13827, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13960_1]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h13818, hlam, p13960_1]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h12794, h13812, h13818, h13820, h13826, h13827, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13960_1]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                rcases p13960_3 (m.d 0 1) (by simp) with h13977 | h13977
                                · linarith only [h11385, h13977, hlam]
                                · linarith only [h13812, h13977, hlam]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h13812, h13820, h13826, h13827, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13960_1]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h13819, hlam, p13960_1]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h13821, hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                rcases p13960_3 (m.d 0 1) (by simp) with h13984 | h13984
                                · linarith only [h12794, h13984, hlam]
                                · linarith only [h13812, h13984, hlam]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h13812, hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h13820, hlam, p13960_1]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h13822, hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [h13823, hlam, p13960_0]
                              · have p13960_0 := h13960c.1
                                have p13960_1 := h13960c.2.1
                                have p13960_2 := h13960c.2.2.1
                                have p13960_3 := h13960c.2.2.2
                                linarith only [hlam, p13960_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13992 | h13992
                            · linarith only [h0, h13813, h13824, h13826, h13992, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases h1bigk with h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c | h13994c
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h0, hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h11385, hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h12794, hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h0, h13823, h13824, h13826, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13994_1]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h13812, h13823, h13824, h13826, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13994_1]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h11385, hc01, hc12, hlam, hphi, p13994_1]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h12794, h13812, h13823, h13824, h13826, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13994_1]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                rcases p13994_3 (m.d 0 1) (by simp) with h14004 | h14004
                                · linarith only [h0, h14004, hlam]
                                · linarith only [h13812, h14004, hlam]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h13812, h13823, h13824, h13826, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13994_1]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h13818, hlam, p13994_1]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h12794, h13812, h13818, h13823, h13824, h13826, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13994_1]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                rcases p13994_3 (m.d 0 1) (by simp) with h14011 | h14011
                                · linarith only [h11385, h14011, hlam]
                                · linarith only [h13812, h14011, hlam]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h13812, h13823, h13824, h13826, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13994_1]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h13819, hlam, p13994_1]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h13821, hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                rcases p13994_3 (m.d 0 1) (by simp) with h14018 | h14018
                                · linarith only [h12794, h14018, hlam]
                                · linarith only [h13812, h14018, hlam]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h13812, hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h13820, hlam, p13994_1]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h13822, hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [h13823, hlam, p13994_0]
                              · have p13994_0 := h13994c.1
                                have p13994_1 := h13994c.2.1
                                have p13994_2 := h13994c.2.2.1
                                have p13994_3 := h13994c.2.2.2
                                linarith only [hlam, p13994_0]
                        · linarith only [h0, h13812, h13822, h13824, h13825, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14027 | h14027
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14028 | h14028
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14029 | h14029
                            · rcases h1bigk with h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c | h14030c
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h0, hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h11385, hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h12794, hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                rcases p14030_3 (m.d 0 1) (by simp) with h14035 | h14035
                                · rcases p14030_3 (m.d 1 2) (by simp) with h14036 | h14036
                                  · rcases p14030_3 (m.d 1 3) (by simp) with h14037 | h14037
                                    · rcases p14030_3 (m.d 1 4) (by simp) with h14038 | h14038
                                      · rcases p14030_3 (m.d 1 5) (by simp) with h14039 | h14039
                                        · linarith only [h14039, hlam, p14030_0]
                                        · rcases h3bigk with h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c | h14041c
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h11385, hlam, p14041_1]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h0, h13813, h14027, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14041_1]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h0, h13813, h13824, h14027, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14041_1]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            rcases p14041_3 (m.d 0 3) (by simp) with h14046 | h14046
                                            · rcases p14041_3 (m.d 1 3) (by simp) with h14047 | h14047
                                              · rcases p14041_3 (m.d 2 3) (by simp) with h14048 | h14048
                                                · linarith only [h13813, h14048, hlam]
                                                · linarith only [h14027, h14048, hlam]
                                              · linarith only [h13822, h14047, hlam]
                                            · linarith only [h14046, hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h11385, h13818, hc01, hc12, hlam, hphi, p14041_1]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13818, h14027, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14041_1]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13818, h13824, h14027, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14041_1]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            rcases p14041_3 (m.d 0 3) (by simp) with h14057 | h14057
                                            · linarith only [h11385, h14057, hlam]
                                            · linarith only [h13816, h14057, hlam]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13813, hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13818, hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13824, hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13815, h13824, h14029, hc03, hc45, hlam, hphi, ht0b, ht5b, p14041_1]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13815, hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13821, hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13815, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14041_1]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h11385, h13815, h13818, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14041_1]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13816, hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h13822, hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h14027, hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [h14029, hlam, p14041_0]
                                          · have p14041_0 := h14041c.1
                                            have p14041_1 := h14041c.2.1
                                            have p14041_2 := h14041c.2.2.1
                                            have p14041_3 := h14041c.2.2.2
                                            linarith only [hlam, p14041_0]
                                      · linarith only [h13823, h14038, hlam]
                                    · linarith only [h13822, h14037, hlam]
                                  · linarith only [h13820, h14036, hlam]
                                · linarith only [h14035, hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                rcases p14030_3 (m.d 0 1) (by simp) with h14079 | h14079
                                · linarith only [h14079, hlam, p14030_0]
                                · rcases p14030_3 (m.d 1 2) (by simp) with h14081 | h14081
                                  · rcases p14030_3 (m.d 1 3) (by simp) with h14082 | h14082
                                    · linarith only [h13818, h14082, hlam]
                                    · linarith only [h11385, h14082, hlam]
                                  · linarith only [h14081, hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h11385, hc01, hc12, hlam, hphi, p14030_1]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h12794, h13812, h13820, h14027, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14030_1]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                rcases p14030_3 (m.d 0 1) (by simp) with h14089 | h14089
                                · linarith only [h0, h14089, hlam]
                                · linarith only [h13812, h14089, hlam]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                rcases p14030_3 (m.d 0 1) (by simp) with h14092 | h14092
                                · linarith only [h14092, hlam, p14030_0]
                                · rcases p14030_3 (m.d 1 2) (by simp) with h14094 | h14094
                                  · rcases p14030_3 (m.d 1 3) (by simp) with h14095 | h14095
                                    · rcases p14030_3 (m.d 1 4) (by simp) with h14096 | h14096
                                      · linarith only [h13821, h14096, hlam]
                                      · linarith only [h12794, h14096, hlam]
                                    · linarith only [h14095, hlam, p14030_0]
                                  · linarith only [h0, h14094, hlam]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h13818, hlam, p14030_1]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h12794, h13815, h13818, h13824, h14027, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14030_1]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                rcases p14030_3 (m.d 0 1) (by simp) with h14104 | h14104
                                · linarith only [h11385, h14104, hlam]
                                · linarith only [h13812, h14104, hlam]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                rcases p14030_3 (m.d 0 1) (by simp) with h14107 | h14107
                                · linarith only [h14107, hlam, p14030_0]
                                · rcases p14030_3 (m.d 1 2) (by simp) with h14109 | h14109
                                  · rcases p14030_3 (m.d 1 3) (by simp) with h14110 | h14110
                                    · rcases p14030_3 (m.d 1 4) (by simp) with h14111 | h14111
                                      · rcases p14030_3 (m.d 1 5) (by simp) with h14112 | h14112
                                        · linarith only [h13823, h14112, hlam]
                                        · rcases h3bigk with h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c | h14114c
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h11385, hlam, p14114_1]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13813, h14027, h14029, hc02, hc45, hlam, hphi, ht0b, ht5b, p14114_1]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13824, h14027, h14029, hc03, hc45, hlam, hphi, ht0b, ht5b, p14114_1]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            rcases p14114_3 (m.d 0 3) (by simp) with h14119 | h14119
                                            · rcases p14114_3 (m.d 1 3) (by simp) with h14120 | h14120
                                              · rcases p14114_3 (m.d 2 3) (by simp) with h14121 | h14121
                                                · linarith only [h13813, h14121, hlam]
                                                · linarith only [h14027, h14121, hlam]
                                              · linarith only [h13822, h14120, hlam]
                                            · linarith only [h14119, hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h11385, h13812, h13818, h13820, h14027, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14114_1]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13818, h14027, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14114_1]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13818, h13824, h14027, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14114_1]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            rcases p14114_3 (m.d 0 3) (by simp) with h14130 | h14130
                                            · linarith only [h11385, h14130, hlam]
                                            · linarith only [h13816, h14130, hlam]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13813, hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13818, hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13824, hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13815, h13824, h14029, hc03, hc45, hlam, hphi, ht0b, ht5b, p14114_1]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13815, hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13821, hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13815, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14114_1]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h11385, h13815, h13818, h14029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14114_1]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13816, hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h13822, hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h14027, hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [h14029, hlam, p14114_0]
                                          · have p14114_0 := h14114c.1
                                            have p14114_1 := h14114c.2.1
                                            have p14114_2 := h14114c.2.2.1
                                            have p14114_3 := h14114c.2.2.2
                                            linarith only [hlam, p14114_0]
                                      · linarith only [h14111, hlam, p14030_0]
                                    · linarith only [h11385, h14110, hlam]
                                  · linarith only [h0, h14109, hlam]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h13819, hlam, p14030_1]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h13821, hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                rcases p14030_3 (m.d 0 1) (by simp) with h14154 | h14154
                                · linarith only [h12794, h14154, hlam]
                                · linarith only [h13812, h14154, hlam]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h13812, hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h13820, hlam, p14030_1]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h13822, hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [h13823, hlam, p14030_0]
                              · have p14030_0 := h14030c.1
                                have p14030_1 := h14030c.2.1
                                have p14030_2 := h14030c.2.2.1
                                have p14030_3 := h14030c.2.2.2
                                linarith only [hlam, p14030_0]
                            · linarith only [h13817, h13824, h14027, h14029, hc04, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h13812, h13823, h13824, h14027, h14028, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14164 | h14164
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14165 | h14165
                            · rcases h1bigk with h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c | h14166c
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h0, hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h11385, hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h12794, hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h12794, h13818, h13821, h13822, h14027, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14166_1]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h13812, h13822, h14027, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14166_1]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h11385, hc01, hc12, hlam, hphi, p14166_1]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h12794, h13812, h13822, h14027, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14166_1]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                rcases p14166_3 (m.d 0 1) (by simp) with h14176 | h14176
                                · linarith only [h0, h14176, hlam]
                                · linarith only [h13812, h14176, hlam]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h13812, h13822, h14027, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14166_1]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h13818, hlam, p14166_1]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h12794, h13812, h13818, h13822, h14027, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14166_1]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                rcases p14166_3 (m.d 0 1) (by simp) with h14183 | h14183
                                · linarith only [h11385, h14183, hlam]
                                · linarith only [h13812, h14183, hlam]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h13812, h13822, h14027, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14166_1]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h13819, hlam, p14166_1]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h13821, hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                rcases p14166_3 (m.d 0 1) (by simp) with h14190 | h14190
                                · linarith only [h12794, h14190, hlam]
                                · linarith only [h13812, h14190, hlam]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h13812, hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h13820, hlam, p14166_1]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h13822, hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [h13823, hlam, p14166_0]
                              · have p14166_0 := h14166c.1
                                have p14166_1 := h14166c.2.1
                                have p14166_2 := h14166c.2.2.1
                                have p14166_3 := h14166c.2.2.2
                                linarith only [hlam, p14166_0]
                            · linarith only [h0, h13814, h13824, h14164, h14165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14199 | h14199
                            · rcases h1bigk with h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c | h14200c
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h0, hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h11385, hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h12794, hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h0, h13822, h13824, h14164, h14199, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14200_1]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h13812, h13822, h13824, h14164, h14199, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14200_1]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h11385, hc01, hc12, hlam, hphi, p14200_1]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h12794, h13812, h13822, h13824, h14164, h14199, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14200_1]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                rcases p14200_3 (m.d 0 1) (by simp) with h14210 | h14210
                                · linarith only [h0, h14210, hlam]
                                · linarith only [h13812, h14210, hlam]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h13812, h13822, h13824, h14164, h14199, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14200_1]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h13818, hlam, p14200_1]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h12794, h13812, h13818, h13822, h13824, h14164, h14199, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14200_1]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                rcases p14200_3 (m.d 0 1) (by simp) with h14217 | h14217
                                · linarith only [h11385, h14217, hlam]
                                · linarith only [h13812, h14217, hlam]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h13812, h13822, h13824, h14164, h14199, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14200_1]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h13819, hlam, p14200_1]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h13821, hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                rcases p14200_3 (m.d 0 1) (by simp) with h14224 | h14224
                                · linarith only [h12794, h14224, hlam]
                                · linarith only [h13812, h14224, hlam]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h13812, hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h13820, hlam, p14200_1]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h13822, hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [h13823, hlam, p14200_0]
                              · have p14200_0 := h14200c.1
                                have p14200_1 := h14200c.2.1
                                have p14200_2 := h14200c.2.2.1
                                have p14200_3 := h14200c.2.2.2
                                linarith only [hlam, p14200_0]
                            · linarith only [h0, h13812, h13823, h13824, h14199, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h12794, h13812, h13817, h13823, hc04, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h11385, h13812, h13816, h13822, hlam]
                · linarith only [h11385, h13815, h13821, hlam]
              · linarith only [h0, h13812, h13820, hlam]
            · linarith only [h11385, h13812, h13814, h13818, h13819, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h13813, h13818, hlam]
        · linarith only [h12794, h13812, h13817, hlam]
      · linarith only [h12794, h13812, h13815, h13816, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14241 | h14241
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14242 | h14242
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14243 | h14243
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14244 | h14244
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14245 | h14245
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14246 | h14246
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14247 | h14247
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14248 | h14248
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14249 | h14249
                      · linarith only [h13813, h13815, h14249, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14251 | h14251
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14252 | h14252
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14253 | h14253
                            · rcases h1bigk with h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c | h14254c
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h0, hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h11385, hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h12794, hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h11385, h13815, h14243, h14245, h14246, h14251, h14253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14254_1]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                rcases p14254_3 (m.d 0 1) (by simp) with h14260 | h14260
                                · linarith only [h14260, hlam, p14254_0]
                                · rcases p14254_3 (m.d 1 2) (by simp) with h14262 | h14262
                                  · rcases p14254_3 (m.d 1 3) (by simp) with h14263 | h14263
                                    · linarith only [h14243, h14263, hlam]
                                    · linarith only [h11385, h14263, hlam]
                                  · linarith only [h14262, hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h11385, h13815, h14246, hc01, hc12, hlam, hphi, p14254_1]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h11385, h13812, h13815, h14245, h14246, h14251, h14253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14254_1]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h11385, h13812, h13815, h14243, h14246, hlam, p14254_2]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                rcases p14254_3 (m.d 0 1) (by simp) with h14271 | h14271
                                · linarith only [h14271, hlam, p14254_0]
                                · rcases p14254_3 (m.d 1 2) (by simp) with h14273 | h14273
                                  · rcases p14254_3 (m.d 1 3) (by simp) with h14274 | h14274
                                    · rcases p14254_3 (m.d 1 4) (by simp) with h14275 | h14275
                                      · linarith only [h14246, h14275, hlam]
                                      · linarith only [h12794, h14275, hlam]
                                    · linarith only [h14274, hlam, p14254_0]
                                  · linarith only [h0, h14273, hlam]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h14243, hlam, p14254_1]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h11385, h13812, h13815, h14243, h14245, h14246, h14251, h14253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14254_1]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h11385, h13812, h13815, h14246, hlam, p14254_2]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                rcases p14254_3 (m.d 0 1) (by simp) with h14284 | h14284
                                · linarith only [h14284, hlam, p14254_0]
                                · rcases p14254_3 (m.d 1 2) (by simp) with h14286 | h14286
                                  · rcases p14254_3 (m.d 1 3) (by simp) with h14287 | h14287
                                    · rcases p14254_3 (m.d 1 4) (by simp) with h14288 | h14288
                                      · rcases p14254_3 (m.d 1 5) (by simp) with h14289 | h14289
                                        · linarith only [h14248, h14289, hlam]
                                        · rcases h3bigk with h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c | h14291c
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h11385, hlam, p14291_1]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h13815, h14246, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14291_1]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h13815, hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h13815, h14246, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p14291_1]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h11385, hc01, hc13, hlam, hphi, p14291_1]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h14243, h14251, h14253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14291_1]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h11385, h13812, h13815, h14243, h14247, h14253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14291_1]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            rcases p14291_3 (m.d 0 3) (by simp) with h14301 | h14301
                                            · linarith only [h11385, h14301, hlam]
                                            · linarith only [h14241, h14301, hlam]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h13813, hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h14243, hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h14249, hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h0, h13813, h14253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14291_1]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h11385, h13812, h14245, h14251, h14253, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14291_1]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h14246, hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h14243, h14246, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14291_1]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h14243, h14246, h14253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14291_1]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h14241, hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h14247, hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h14251, hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [h14253, hlam, p14291_0]
                                          · have p14291_0 := h14291c.1
                                            have p14291_1 := h14291c.2.1
                                            have p14291_2 := h14291c.2.2.1
                                            have p14291_3 := h14291c.2.2.2
                                            linarith only [hlam, p14291_0]
                                      · linarith only [h14288, hlam, p14254_0]
                                    · linarith only [h11385, h14287, hlam]
                                  · linarith only [h0, h14286, hlam]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h14244, hlam, p14254_1]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h14246, hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                rcases p14254_3 (m.d 0 1) (by simp) with h14325 | h14325
                                · linarith only [h12794, h14325, hlam]
                                · linarith only [h13812, h14325, hlam]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h13812, hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h14245, hlam, p14254_1]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h14247, hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [h14248, hlam, p14254_0]
                              · have p14254_0 := h14254c.1
                                have p14254_1 := h14254c.2.1
                                have p14254_2 := h14254c.2.2.1
                                have p14254_3 := h14254c.2.2.2
                                linarith only [hlam, p14254_0]
                            · linarith only [h11385, h13812, h13815, h14242, h14245, h14251, h14253, hc04, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h11385, h13812, h13815, h14243, h14246, h14248, h14252, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h13815, h14241, h14243, h14246, h14251, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h12794, h14242, h14248, hlam]
                  · linarith only [h13815, h14241, h14247, hc13, hc34, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14338 | h14338
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14339 | h14339
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14340 | h14340
                      · linarith only [h11385, h14246, h14340, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14342 | h14342
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14343 | h14343
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14344 | h14344
                            · rcases h1bigk with h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c | h14345c
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h0, hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h11385, hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h12794, hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h11385, h14245, h14246, h14342, h14344, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14345_1]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                rcases p14345_3 (m.d 0 1) (by simp) with h14351 | h14351
                                · linarith only [h14351, hlam, p14345_0]
                                · rcases p14345_3 (m.d 1 2) (by simp) with h14353 | h14353
                                  · rcases p14345_3 (m.d 1 3) (by simp) with h14354 | h14354
                                    · linarith only [h14243, h14354, hlam]
                                    · linarith only [h11385, h14354, hlam]
                                  · linarith only [h14353, hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h11385, hc01, hc12, hlam, hphi, p14345_1]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h12794, h13812, h14245, h14342, h14344, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14345_1]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                rcases p14345_3 (m.d 0 1) (by simp) with h14361 | h14361
                                · linarith only [h0, h14361, hlam]
                                · linarith only [h13812, h14361, hlam]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h13812, h14245, h14246, h14342, h14344, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14345_1]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h14243, hlam, p14345_1]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h14246, hlam, p14345_1]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                rcases p14345_3 (m.d 0 1) (by simp) with h14368 | h14368
                                · linarith only [h11385, h14368, hlam]
                                · linarith only [h13812, h14368, hlam]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                rcases p14345_3 (m.d 0 1) (by simp) with h14371 | h14371
                                · linarith only [h14371, hlam, p14345_0]
                                · rcases p14345_3 (m.d 1 2) (by simp) with h14373 | h14373
                                  · rcases p14345_3 (m.d 1 3) (by simp) with h14374 | h14374
                                    · linarith only [h14246, h14374, hlam]
                                    · linarith only [h11385, h14374, hlam]
                                  · linarith only [h0, h14373, hlam]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h14244, hlam, p14345_1]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h11385, h13812, h14244, h14245, h14342, h14344, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14345_1]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                rcases p14345_3 (m.d 0 1) (by simp) with h14381 | h14381
                                · linarith only [h12794, h14381, hlam]
                                · linarith only [h13812, h14381, hlam]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h13812, hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h14245, hlam, p14345_1]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h14338, hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [h14339, hlam, p14345_0]
                              · have p14345_0 := h14345c.1
                                have p14345_1 := h14345c.2.1
                                have p14345_2 := h14345c.2.2.1
                                have p14345_3 := h14345c.2.2.2
                                linarith only [hlam, p14345_0]
                            · linarith only [h13815, h14242, h14344, hlam]
                          · linarith only [h11385, h13812, h14339, h14340, h14342, h14343, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h11385, h14241, h14246, h14342, hc23, hc34, hlam, hphi]
                    · linarith only [h12794, h14242, h14339, hlam]
                  · linarith only [h11385, h14241, h14338, hlam]
              · linarith only [h0, h13812, h14245, hlam]
            · linarith only [h11385, h13812, h13814, h14243, h14244, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h13813, h14243, hlam]
        · linarith only [h11385, h13812, h13815, h14242, hlam]
      · linarith only [h11385, h13812, h14241, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14399 | h14399
    · linarith only [h13813, h13814, h14399, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14401 | h14401
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14402 | h14402
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14403 | h14403
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14404 | h14404
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14405 | h14405
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14406 | h14406
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14407 | h14407
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14408 | h14408
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14409 | h14409
                      · linarith only [h13813, h13814, h14399, h14404, h14409, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14411 | h14411
                        · linarith only [h13813, h13814, h14403, h14406, h14409, h14411, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h13813, h13814, h14401, h14403, h14406, h14409, h14411, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h12794, h13812, h14402, h14405, h14408, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h14399, h14401, h14407, hc13, hc34, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14416 | h14416
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14417 | h14417
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14418 | h14418
                      · linarith only [h13813, h13814, h14404, h14418, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14420 | h14420
                        · linarith only [h13813, h13814, h14404, h14420, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h13813, h13814, h14401, h14404, h14420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h13813, h13814, h14404, h14417, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h11385, h13812, h13813, h14401, h14405, h14416, hc02, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h13814, h14404, h14405, hc02, hc25, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14426 | h14426
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14427 | h14427
                · linarith only [h11385, h14399, h14403, h14404, h14427, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14429 | h14429
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14430 | h14430
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14431 | h14431
                      · linarith only [h0, h13813, h14404, h14427, h14431, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14433 | h14433
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14434 | h14434
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14435 | h14435
                            · rcases h1bigk with h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c | h14436c
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h0, hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h11385, hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h12794, hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h0, h14404, h14426, h14431, h14433, h14435, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14436_1]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h14404, h14431, hc01, hc34, hlam, hphi, ht12, ht23, p14436_1]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h11385, h13812, h14404, h14426, h14431, h14433, h14435, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14436_1]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h14404, hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                rcases p14436_3 (m.d 0 1) (by simp) with h14446 | h14446
                                · linarith only [h0, h14446, hlam]
                                · linarith only [h13812, h14446, hlam]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h13812, h14403, h14404, h14426, h14431, h14433, h14435, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14436_1]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h14403, hlam, p14436_1]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h14427, hlam, p14436_1]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                rcases p14436_3 (m.d 0 1) (by simp) with h14453 | h14453
                                · linarith only [h11385, h14453, hlam]
                                · linarith only [h13812, h14453, hlam]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                rcases p14436_3 (m.d 0 1) (by simp) with h14456 | h14456
                                · linarith only [h14456, hlam, p14436_0]
                                · rcases p14436_3 (m.d 1 2) (by simp) with h14458 | h14458
                                  · linarith only [h14404, h14458, hlam]
                                  · linarith only [h0, h14458, hlam]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h0, h13813, h14404, h14431, hc23, hc34, hlam, hphi, p14436_1]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h11385, h13812, h14404, h14426, h14431, h14433, h14435, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14436_1]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                rcases p14436_3 (m.d 0 1) (by simp) with h14464 | h14464
                                · linarith only [h12794, h14464, hlam]
                                · linarith only [h13812, h14464, hlam]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h13812, hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h14426, hlam, p14436_1]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h14429, hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [h14430, hlam, p14436_0]
                              · have p14436_0 := h14436c.1
                                have p14436_1 := h14436c.2.1
                                have p14436_2 := h14436c.2.2.1
                                have p14436_3 := h14436c.2.2.2
                                linarith only [hlam, p14436_0]
                            · linarith only [h13813, h13814, h14431, h14433, h14435, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h11385, h13812, h14403, h14404, h14430, h14434, hlam]
                        · linarith only [h0, h13813, h14401, h14404, h14431, h14433, hc23, hc34, hlam, hphi]
                    · linarith only [h12794, h14402, h14430, hlam]
                  · linarith only [h0, h11385, h13812, h13813, h14401, h14404, h14426, h14429, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h11385, h13812, h14403, h14426, hlam]
          · linarith only [h0, h13813, h14403, hlam]
        · linarith only [h0, h13812, h13814, h14402, hlam]
      · linarith only [h11385, h13812, h14401, hlam]

end R2N4
