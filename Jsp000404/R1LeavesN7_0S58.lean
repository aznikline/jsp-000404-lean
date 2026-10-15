import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 2) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 2) ∧ (m.d 1 5) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 5) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  rcases p20349_3 (m.d 0 1) (by simp) with h20858 | h20858
  · rcases p20349_3 (m.d 1 2) (by simp) with h20859 | h20859
    · rcases p20349_3 (m.d 1 3) (by simp) with h20860 | h20860
      · rcases p20349_3 (m.d 1 4) (by simp) with h20861 | h20861
        · linarith only [h20337, h20861, hlam]
        · rcases p20349_3 (m.d 1 5) (by simp) with h20863 | h20863
          · linarith only [h20338, h20863, hlam]
          · rcases h1emax with h20865 | h20865 | h20865 | h20865 | h20865
            · linarith only [h0, h20341, h20865, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p20349_1]
            · linarith only [h20337, h20341, h20343, h20865, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20349_1]
            · linarith only [h20335, h20337, h20341, h20343, h20865, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20349_1]
            · rcases h2bigk with h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c | h20869c
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h20337, h20341, h20343, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p20869_1]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h4, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                rcases p20869_3 (m.d 0 2) (by simp) with h20873 | h20873
                · rcases p20869_3 (m.d 1 2) (by simp) with h20874 | h20874
                  · linarith only [h0, h20874, hlam]
                  · linarith only [h20337, h20874, hlam]
                · linarith only [h20873, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                rcases p20869_3 (m.d 0 2) (by simp) with h20878 | h20878
                · rcases p20869_3 (m.d 1 2) (by simp) with h20879 | h20879
                  · linarith only [h0, h20879, hlam]
                  · linarith only [h20338, h20879, hlam]
                · linarith only [h20878, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h0, hlam, p20869_1]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h20335, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                rcases p20869_3 (m.d 0 2) (by simp) with h20886 | h20886
                · rcases p20869_3 (m.d 1 2) (by simp) with h20887 | h20887
                  · rcases p20869_3 (m.d 2 3) (by simp) with h20888 | h20888
                    · rcases p20869_3 (m.d 2 4) (by simp) with h20889 | h20889
                      · linarith only [h20889, hlam, p20869_0]
                      · rcases p20869_3 (m.d 2 5) (by simp) with h20891 | h20891
                        · linarith only [h20338, h20891, hlam]
                        · linarith only [h20345, h20891, hlam]
                    · linarith only [h20343, h20888, hlam]
                  · linarith only [h20887, hlam, p20869_0]
                · linarith only [h19744, h20886, hlam]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                rcases p20869_3 (m.d 0 2) (by simp) with h20897 | h20897
                · rcases p20869_3 (m.d 1 2) (by simp) with h20898 | h20898
                  · rcases p20869_3 (m.d 2 3) (by simp) with h20899 | h20899
                    · rcases p20869_3 (m.d 2 4) (by simp) with h20900 | h20900
                      · linarith only [h20337, h20900, hlam]
                      · rcases p20869_3 (m.d 2 5) (by simp) with h20902 | h20902
                        · linarith only [h20902, hlam, p20869_0]
                        · rcases h4bigk with h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c | h20904c
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h19748, h20337, h20343, hc34, hc45, hlam, hphi, p20904_1]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h19748, h20343, hc34, hc45, hlam, hphi, p20904_1]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h19748, hc34, hc45, hlam, hphi, p20904_1]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h19748, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h2, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h1, h20335, h20341, h20343, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p20904_1]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h0, h20341, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p20904_1]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h20341, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h19744, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h20337, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h19744, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20904_1]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h20345, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h19746, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h20339, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h20343, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [h20347, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            rcases p20904_3 (m.d 0 4) (by simp) with h20925 | h20925
                            · linarith only [h20925, hlam, p20904_0]
                            · rcases p20904_3 (m.d 1 4) (by simp) with h20927 | h20927
                              · linarith only [h20341, h20927, hlam]
                              · rcases p20904_3 (m.d 2 4) (by simp) with h20929 | h20929
                                · linarith only [h20345, h20929, hlam]
                                · rcases p20904_3 (m.d 3 4) (by simp) with h20931 | h20931
                                  · linarith only [h20347, h20931, hlam]
                                  · rcases p20904_3 (m.d 4 5) (by simp) with h20933 | h20933
                                    · rcases h5bigk with h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c | h20934c
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [hlam, p20934_0]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h19745, h20341, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h19745, h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h19745, h20347, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h19748, hlam, p20934_0]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h3, hlam, p20934_0]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [hlam, p20934_0]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h3, hc01, hc25, hlam, hphi, ht0b, ht5b, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h0, h20347, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h20341, hlam, p20934_0]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h19745, hlam, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h20338, hlam, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [hlam, p20934_0]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h19745, h20347, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h20345, hlam, p20934_0]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h19747, hlam, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h20340, hlam, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h20344, hlam, p20934_0]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [hlam, p20934_0]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h20347, hlam, p20934_0]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h19747, h20347, hc34, hc45, hlam, hphi, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h20340, h20347, hc34, hc45, hlam, hphi, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h20344, h20347, hc34, hc45, hlam, hphi, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [h20347, hc34, hc45, hlam, hphi, p20934_1]
                                      · have p20934_0 := h20934c.1
                                        have p20934_1 := h20934c.2.1
                                        have p20934_2 := h20934c.2.2.1
                                        have p20934_3 := h20934c.2.2.2
                                        linarith only [hlam, p20934_0]
                                    · linarith only [h20933, hlam, p20904_0]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            rcases p20904_3 (m.d 0 4) (by simp) with h20961 | h20961
                            · linarith only [h19748, h20961, hlam]
                            · linarith only [h2, h20961, hlam]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            rcases p20904_3 (m.d 0 4) (by simp) with h20964 | h20964
                            · linarith only [h19748, h20964, hlam]
                            · linarith only [h19744, h20964, hlam]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            rcases p20904_3 (m.d 0 4) (by simp) with h20967 | h20967
                            · linarith only [h19748, h20967, hlam]
                            · linarith only [h19746, h20967, hlam]
                          · have p20904_0 := h20904c.1
                            have p20904_1 := h20904c.2.1
                            have p20904_2 := h20904c.2.2.1
                            have p20904_3 := h20904c.2.2.2
                            linarith only [hlam, p20904_0]
                    · linarith only [h20344, h20899, hlam]
                  · linarith only [h20898, hlam, p20869_0]
                · linarith only [h19745, h20897, hlam]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h0, h20337, h20341, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p20869_1]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h20337, h20341, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p20869_1]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h0, h20337, h20341, h4, hlam, p20349_1, p20869_2]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h0, h20338, h4, hlam, p20349_1, p20869_2]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h19744, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h20337, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h20343, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h20345, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h19745, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h20338, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h20344, hlam, p20869_0]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [h0, h20338, h20343, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p20869_1]
              · have p20869_0 := h20869c.1
                have p20869_1 := h20869c.2.1
                have p20869_2 := h20869c.2.2.1
                have p20869_3 := h20869c.2.2.2
                linarith only [hlam, p20869_0]
            · rcases h2bigk with h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c | h20989c
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h4, hc12, hc23, hlam, hphi, p20989_1]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h4, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                rcases p20989_3 (m.d 0 2) (by simp) with h20993 | h20993
                · rcases p20989_3 (m.d 1 2) (by simp) with h20994 | h20994
                  · linarith only [h0, h20994, hlam]
                  · linarith only [h20337, h20994, hlam]
                · linarith only [h20993, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                rcases p20989_3 (m.d 0 2) (by simp) with h20998 | h20998
                · rcases p20989_3 (m.d 1 2) (by simp) with h20999 | h20999
                  · linarith only [h0, h20999, hlam]
                  · linarith only [h20338, h20999, hlam]
                · linarith only [h20998, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h0, hlam, p20989_1]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h20335, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                rcases p20989_3 (m.d 0 2) (by simp) with h21006 | h21006
                · rcases p20989_3 (m.d 1 2) (by simp) with h21007 | h21007
                  · rcases p20989_3 (m.d 2 3) (by simp) with h21008 | h21008
                    · rcases p20989_3 (m.d 2 4) (by simp) with h21009 | h21009
                      · linarith only [h21009, hlam, p20989_0]
                      · rcases p20989_3 (m.d 2 5) (by simp) with h21011 | h21011
                        · linarith only [h20338, h21011, hlam]
                        · linarith only [h20345, h21011, hlam]
                    · linarith only [h20343, h21008, hlam]
                  · linarith only [h21007, hlam, p20989_0]
                · linarith only [h19744, h21006, hlam]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                rcases p20989_3 (m.d 0 2) (by simp) with h21017 | h21017
                · rcases p20989_3 (m.d 1 2) (by simp) with h21018 | h21018
                  · rcases p20989_3 (m.d 2 3) (by simp) with h21019 | h21019
                    · rcases p20989_3 (m.d 2 4) (by simp) with h21020 | h21020
                      · linarith only [h20337, h21020, hlam]
                      · rcases p20989_3 (m.d 2 5) (by simp) with h21022 | h21022
                        · linarith only [h21022, hlam, p20989_0]
                        · rcases h4bigk with h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c | h21024c
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h19748, h20337, h20343, hc34, hc45, hlam, hphi, p21024_1]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h19748, h20343, hc34, hc45, hlam, hphi, p21024_1]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h19748, hc34, hc45, hlam, hphi, p21024_1]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h19748, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h2, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h20341, h20343, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20349_1, p21024_1]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h0, h20341, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p21024_1]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h20341, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h19744, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h20337, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h19744, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21024_1]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h20345, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h19746, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h20339, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h20343, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [h20347, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            rcases p21024_3 (m.d 0 4) (by simp) with h21045 | h21045
                            · linarith only [h21045, hlam, p21024_0]
                            · rcases p21024_3 (m.d 1 4) (by simp) with h21047 | h21047
                              · linarith only [h20341, h21047, hlam]
                              · rcases p21024_3 (m.d 2 4) (by simp) with h21049 | h21049
                                · linarith only [h20345, h21049, hlam]
                                · rcases p21024_3 (m.d 3 4) (by simp) with h21051 | h21051
                                  · linarith only [h20347, h21051, hlam]
                                  · rcases p21024_3 (m.d 4 5) (by simp) with h21053 | h21053
                                    · rcases h5bigk with h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c | h21054c
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [hlam, p21054_0]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h19745, h20341, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h19745, h20345, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h19745, h20347, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h19748, hlam, p21054_0]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h3, hlam, p21054_0]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [hlam, p21054_0]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h20345, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h0, h20347, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h20341, hlam, p21054_0]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h19745, hlam, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h20338, hlam, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [hlam, p21054_0]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h19745, h20347, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h20345, hlam, p21054_0]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h19747, hlam, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h20340, hlam, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h20344, hlam, p21054_0]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [hlam, p21054_0]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h20347, hlam, p21054_0]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h19747, h20347, hc34, hc45, hlam, hphi, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h20340, h20347, hc34, hc45, hlam, hphi, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h20344, h20347, hc34, hc45, hlam, hphi, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [h20347, hc34, hc45, hlam, hphi, p21054_1]
                                      · have p21054_0 := h21054c.1
                                        have p21054_1 := h21054c.2.1
                                        have p21054_2 := h21054c.2.2.1
                                        have p21054_3 := h21054c.2.2.2
                                        linarith only [hlam, p21054_0]
                                    · linarith only [h21053, hlam, p21024_0]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            rcases p21024_3 (m.d 0 4) (by simp) with h21081 | h21081
                            · linarith only [h19748, h21081, hlam]
                            · linarith only [h2, h21081, hlam]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            rcases p21024_3 (m.d 0 4) (by simp) with h21084 | h21084
                            · linarith only [h19748, h21084, hlam]
                            · linarith only [h19744, h21084, hlam]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            rcases p21024_3 (m.d 0 4) (by simp) with h21087 | h21087
                            · linarith only [h19748, h21087, hlam]
                            · linarith only [h19746, h21087, hlam]
                          · have p21024_0 := h21024c.1
                            have p21024_1 := h21024c.2.1
                            have p21024_2 := h21024c.2.2.1
                            have p21024_3 := h21024c.2.2.2
                            linarith only [hlam, p21024_0]
                    · linarith only [h20344, h21019, hlam]
                  · linarith only [h21018, hlam, p20989_0]
                · linarith only [h19745, h21017, hlam]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h0, h20337, h20341, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p20989_1]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h20337, h20341, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p20989_1]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h0, h20337, h20341, h4, hlam, p20349_1, p20989_2]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h0, h20338, h4, hlam, p20349_1, p20989_2]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h19744, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h20337, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h20343, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h20345, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h19745, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h20338, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h20344, hlam, p20989_0]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [h0, h20338, h20343, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p20989_1]
              · have p20989_0 := h20989c.1
                have p20989_1 := h20989c.2.1
                have p20989_2 := h20989c.2.2.1
                have p20989_3 := h20989c.2.2.2
                linarith only [hlam, p20989_0]
      · linarith only [h20340, h20860, hlam]
    · linarith only [h20338, h20859, hlam]
  · linarith only [h20858, h3, hlam]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 3) ∧ (m.d 0 1) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 0 1) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h1, hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 3) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 3) ∧ (m.d 1 2) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 2) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h1, h20337, h20343, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 3) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 3) ∧ (m.d 1 3) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 3) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 3) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 3) ∧ (m.d 1 4) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 4) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  rcases p20349_3 (m.d 0 1) (by simp) with h21115 | h21115
  · rcases p20349_3 (m.d 1 2) (by simp) with h21116 | h21116
    · linarith only [h20335, h21116, hlam]
    · linarith only [h20337, h21116, hlam]
  · linarith only [h2, h21115, hlam]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x14 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 3) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 3) ∧ (m.d 1 5) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 5) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  rcases p20349_3 (m.d 0 1) (by simp) with h21120 | h21120
  · rcases p20349_3 (m.d 1 2) (by simp) with h21121 | h21121
    · linarith only [h20335, h21121, hlam]
    · linarith only [h20338, h21121, hlam]
  · linarith only [h21120, h3, hlam]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x15 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 4) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 4) ∧ (m.d 0 1) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 0 1) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h2, hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x16 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 4) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 4) ∧ (m.d 1 2) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 2) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h20337, hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x17 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 4) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 4) ∧ (m.d 1 3) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 3) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h20339, hlam, p20349_1]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x18 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 4) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 4) ∧ (m.d 1 4) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 4) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x19 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 4) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 4) ∧ (m.d 1 5) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 5) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h20341, hlam, p20349_1]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x20 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 5) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 5) ∧ (m.d 0 1) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 0 1) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h3, hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x21 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 5) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 5) ∧ (m.d 1 2) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 2) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h20338, hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x22 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 5) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 5) ∧ (m.d 1 3) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 3) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h20340, hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x23 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 5) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 5) ∧ (m.d 1 4) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 4) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  rcases p20349_3 (m.d 0 1) (by simp) with h21133 | h21133
  · rcases p20349_3 (m.d 1 2) (by simp) with h21134 | h21134
    · rcases p20349_3 (m.d 1 3) (by simp) with h21135 | h21135
      · rcases p20349_3 (m.d 1 4) (by simp) with h21136 | h21136
        · linarith only [h20341, h21136, hlam]
        · rcases p20349_3 (m.d 1 5) (by simp) with h21138 | h21138
          · rcases h1emax with h21139 | h21139 | h21139 | h21139 | h21139
            · linarith only [h0, h20338, h21139, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h20337, h20338, h20343, h21139, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20349_1]
            · linarith only [h20335, h20337, h20338, h20343, h21139, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20349_1]
            · rcases h2bigk with h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c | h21143c
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h20337, h20338, h20343, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p21143_1]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h4, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                rcases p21143_3 (m.d 0 2) (by simp) with h21147 | h21147
                · rcases p21143_3 (m.d 1 2) (by simp) with h21148 | h21148
                  · linarith only [h0, h21148, hlam]
                  · linarith only [h20337, h21148, hlam]
                · linarith only [h21147, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                rcases p21143_3 (m.d 0 2) (by simp) with h21152 | h21152
                · rcases p21143_3 (m.d 1 2) (by simp) with h21153 | h21153
                  · linarith only [h0, h21153, hlam]
                  · linarith only [h20338, h21153, hlam]
                · linarith only [h21152, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h0, hlam, p21143_1]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h20335, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                rcases p21143_3 (m.d 0 2) (by simp) with h21160 | h21160
                · rcases p21143_3 (m.d 1 2) (by simp) with h21161 | h21161
                  · rcases p21143_3 (m.d 2 3) (by simp) with h21162 | h21162
                    · rcases p21143_3 (m.d 2 4) (by simp) with h21163 | h21163
                      · linarith only [h21163, hlam, p21143_0]
                      · rcases p21143_3 (m.d 2 5) (by simp) with h21165 | h21165
                        · linarith only [h20338, h21165, hlam]
                        · linarith only [h20345, h21165, hlam]
                    · linarith only [h20343, h21162, hlam]
                  · linarith only [h21161, hlam, p21143_0]
                · linarith only [h19744, h21160, hlam]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                rcases p21143_3 (m.d 0 2) (by simp) with h21171 | h21171
                · rcases p21143_3 (m.d 1 2) (by simp) with h21172 | h21172
                  · rcases p21143_3 (m.d 2 3) (by simp) with h21173 | h21173
                    · rcases p21143_3 (m.d 2 4) (by simp) with h21174 | h21174
                      · linarith only [h20337, h21174, hlam]
                      · rcases p21143_3 (m.d 2 5) (by simp) with h21176 | h21176
                        · linarith only [h21176, hlam, p21143_0]
                        · rcases h4bigk with h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c | h21178c
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h19748, h20337, h20343, hc34, hc45, hlam, hphi, p21178_1]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h19748, h20343, hc34, hc45, hlam, hphi, p21178_1]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h19748, hc34, hc45, hlam, hphi, p21178_1]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h19748, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h2, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h1, h20335, h20338, h20343, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p21178_1]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h0, h20338, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p21178_1]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h20341, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h19744, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h20337, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h19744, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21178_1]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h20345, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h19746, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h20339, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h20343, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [h20347, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            rcases p21178_3 (m.d 0 4) (by simp) with h21199 | h21199
                            · linarith only [h21199, hlam, p21178_0]
                            · rcases p21178_3 (m.d 1 4) (by simp) with h21201 | h21201
                              · linarith only [h20341, h21201, hlam]
                              · rcases p21178_3 (m.d 2 4) (by simp) with h21203 | h21203
                                · linarith only [h20345, h21203, hlam]
                                · rcases p21178_3 (m.d 3 4) (by simp) with h21205 | h21205
                                  · linarith only [h20347, h21205, hlam]
                                  · rcases p21178_3 (m.d 4 5) (by simp) with h21207 | h21207
                                    · rcases h5bigk with h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c | h21208c
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [hlam, p21208_0]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h19745, h20345, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h19745, h20347, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h19748, hlam, p21208_0]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h3, hlam, p21208_0]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [hlam, p21208_0]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h20345, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h19745, h20347, h3, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h20341, hlam, p21208_0]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h19745, hlam, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h20338, hlam, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [hlam, p21208_0]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h19745, h20347, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h20345, hlam, p21208_0]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h19747, hlam, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h20340, hlam, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h20344, hlam, p21208_0]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [hlam, p21208_0]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h20347, hlam, p21208_0]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h19747, h20347, hc34, hc45, hlam, hphi, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h20340, h20347, hc34, hc45, hlam, hphi, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h20344, h20347, hc34, hc45, hlam, hphi, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [h20347, hc34, hc45, hlam, hphi, p21208_1]
                                      · have p21208_0 := h21208c.1
                                        have p21208_1 := h21208c.2.1
                                        have p21208_2 := h21208c.2.2.1
                                        have p21208_3 := h21208c.2.2.2
                                        linarith only [hlam, p21208_0]
                                    · linarith only [h21207, hlam, p21178_0]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            rcases p21178_3 (m.d 0 4) (by simp) with h21235 | h21235
                            · linarith only [h19748, h21235, hlam]
                            · linarith only [h2, h21235, hlam]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            rcases p21178_3 (m.d 0 4) (by simp) with h21238 | h21238
                            · linarith only [h19748, h21238, hlam]
                            · linarith only [h19744, h21238, hlam]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            rcases p21178_3 (m.d 0 4) (by simp) with h21241 | h21241
                            · linarith only [h19748, h21241, hlam]
                            · linarith only [h19746, h21241, hlam]
                          · have p21178_0 := h21178c.1
                            have p21178_1 := h21178c.2.1
                            have p21178_2 := h21178c.2.2.1
                            have p21178_3 := h21178c.2.2.2
                            linarith only [hlam, p21178_0]
                    · linarith only [h20344, h21173, hlam]
                  · linarith only [h21172, hlam, p21143_0]
                · linarith only [h19745, h21171, hlam]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h19745, h20337, h20343, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p21143_1]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h20337, h20338, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20349_1, p21143_1]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h19745, h20337, h3, h4, hlam, p20349_1, p21143_2]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                rcases p21143_3 (m.d 0 2) (by simp) with h21252 | h21252
                · linarith only [h21252, h4, hlam]
                · linarith only [h19745, h21252, hlam]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h19744, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h20337, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h20343, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h20345, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h19745, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h20338, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h20344, hlam, p21143_0]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [h19745, h20343, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21143_1]
              · have p21143_0 := h21143c.1
                have p21143_1 := h21143c.2.1
                have p21143_2 := h21143c.2.2.1
                have p21143_3 := h21143c.2.2.2
                linarith only [hlam, p21143_0]
            · linarith only [h20337, h20343, h21139, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20349_1]
          · linarith only [h20341, h21138, hlam]
      · linarith only [h20339, h21135, hlam]
    · linarith only [h20337, h21134, hlam]
  · linarith only [h2, h21133, hlam]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x24 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 5) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 5) ∧ (m.d 1 5) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 5) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [hlam, p20349_0]

end R2N4
