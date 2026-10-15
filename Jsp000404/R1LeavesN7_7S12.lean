import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 0 4 5 (by decide) (by decide) with h7873 | h7873
  · linarith only [h6418, h6419, h7873, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7875 | h7875
    · linarith only [h0, h4, h7875, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7877 | h7877
      · linarith only [h0, h5543, h7877, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7879 | h7879
        · linarith only [h0, h6343, h7879, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7881 | h7881
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7882 | h7882
            · linarith only [h1, h6419, h7882, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7884 | h7884
              · linarith only [h2, h6418, h6419, h7873, h7884, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7886 | h7886
                · rcases m.htr 2 3 5 (by decide) (by decide) with h7887 | h7887
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7888 | h7888
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7889 | h7889
                      · linarith only [h1, h6419, h7873, h7881, h7887, h7889, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases h1bigk with h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c | h7891c
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          rcases p7891_3 (m.d 0 1) (by simp) with h7893 | h7893
                          · rcases p7891_3 (m.d 1 2) (by simp) with h7894 | h7894
                            · linarith only [h7894, hlam, p7891_0]
                            · rcases p7891_3 (m.d 1 3) (by simp) with h7896 | h7896
                              · linarith only [h1, h7896, hlam]
                              · linarith only [h7875, h7896, hlam]
                          · linarith only [h7893, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          rcases p7891_3 (m.d 0 1) (by simp) with h7900 | h7900
                          · rcases p7891_3 (m.d 1 2) (by simp) with h7901 | h7901
                            · linarith only [h0, h7901, hlam]
                            · rcases p7891_3 (m.d 1 3) (by simp) with h7903 | h7903
                              · linarith only [h7903, hlam, p7891_0]
                              · rcases p7891_3 (m.d 1 4) (by simp) with h7905 | h7905
                                · linarith only [h2, h7905, hlam]
                                · rcases p7891_3 (m.d 1 5) (by simp) with h7907 | h7907
                                  · linarith only [h3, h7907, hlam]
                                  · linarith only [h7882, h7907, hlam]
                          · linarith only [h7900, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          rcases p7891_3 (m.d 0 1) (by simp) with h7911 | h7911
                          · rcases p7891_3 (m.d 1 2) (by simp) with h7912 | h7912
                            · linarith only [h0, h7912, hlam]
                            · rcases p7891_3 (m.d 1 3) (by simp) with h7914 | h7914
                              · linarith only [h1, h7914, hlam]
                              · linarith only [h7881, h7914, hlam]
                          · linarith only [h7911, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          rcases p7891_3 (m.d 0 1) (by simp) with h7918 | h7918
                          · rcases p7891_3 (m.d 1 2) (by simp) with h7919 | h7919
                            · linarith only [h0, h7919, hlam]
                            · rcases p7891_3 (m.d 1 3) (by simp) with h7921 | h7921
                              · linarith only [h1, h7921, hlam]
                              · rcases p7891_3 (m.d 1 4) (by simp) with h7923 | h7923
                                · linarith only [h2, h7923, hlam]
                                · rcases p7891_3 (m.d 1 5) (by simp) with h7925 | h7925
                                  · linarith only [h7925, hlam, p7891_0]
                                  · rcases h1emax with h7927 | h7927 | h7927 | h7927 | h7927
                                    · linarith only [h1, h7881, h7927, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h3bigk with h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h6419, h7881, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7929_1]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h4, hlam, p7929_1]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h6419, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7929_1]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h6419, hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h1, hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h7875, hlam, p7929_1]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h7882, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7891_1, p7929_1]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h7882, hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        rcases p7929_3 (m.d 0 3) (by simp) with h7940 | h7940
                                        · linarith only [h4, h7940, hlam]
                                        · rcases p7929_3 (m.d 1 3) (by simp) with h7942 | h7942
                                          · linarith only [h7875, h7942, hlam]
                                          · rcases p7929_3 (m.d 2 3) (by simp) with h7944 | h7944
                                            · rcases p7929_3 (m.d 3 4) (by simp) with h7945 | h7945
                                              · linarith only [h7886, h7945, hlam]
                                              · rcases p7929_3 (m.d 3 5) (by simp) with h7947 | h7947
                                                · linarith only [h7887, h7947, hlam]
                                                · linarith only [h6419, h7947, hlam]
                                            · linarith only [h4, h7944, hlam]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        rcases p7929_3 (m.d 0 3) (by simp) with h7951 | h7951
                                        · linarith only [h4, h7951, hlam]
                                        · linarith only [h1, h7951, hlam]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h6418, h6419, h7886, h7888, h7889, hlam, p7929_2]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h1, h6419, h7881, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7929_1]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h6418, hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h7881, hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h7886, hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h7889, hlam, p7929_1]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h1, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7929_1]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7929_1]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [h7887, hlam, p7929_0]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        rcases p7929_3 (m.d 0 3) (by simp) with h7965 | h7965
                                        · linarith only [h6419, h7965, hlam]
                                        · linarith only [h6418, h7965, hlam]
                                      · have p7929_0 := h7929c.1
                                        have p7929_1 := h7929c.2.1
                                        have p7929_2 := h7929c.2.2.1
                                        have p7929_3 := h7929c.2.2.2
                                        linarith only [hlam, p7929_0]
                                    · rcases h3bigk with h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c | h7969c
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h6419, h7881, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7969_1]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h4, hlam, p7969_1]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h6419, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7969_1]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h6419, hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h1, hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h7875, hlam, p7969_1]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h1, h6419, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7969_1]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h7882, hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        rcases p7969_3 (m.d 0 3) (by simp) with h7980 | h7980
                                        · linarith only [h4, h7980, hlam]
                                        · rcases p7969_3 (m.d 1 3) (by simp) with h7982 | h7982
                                          · linarith only [h7875, h7982, hlam]
                                          · rcases p7969_3 (m.d 2 3) (by simp) with h7984 | h7984
                                            · rcases p7969_3 (m.d 3 4) (by simp) with h7985 | h7985
                                              · linarith only [h7886, h7985, hlam]
                                              · rcases p7969_3 (m.d 3 5) (by simp) with h7987 | h7987
                                                · linarith only [h7887, h7987, hlam]
                                                · linarith only [h6419, h7987, hlam]
                                            · linarith only [h4, h7984, hlam]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        rcases p7969_3 (m.d 0 3) (by simp) with h7991 | h7991
                                        · linarith only [h4, h7991, hlam]
                                        · linarith only [h1, h7991, hlam]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h6418, h6419, h7886, h7888, h7889, hlam, p7969_2]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h1, h6419, h7881, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7969_1]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h6418, hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h7881, hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h7886, hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h7889, hlam, p7969_1]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h1, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7969_1]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7969_1]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [h7887, hlam, p7969_0]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        rcases p7969_3 (m.d 0 3) (by simp) with h8005 | h8005
                                        · linarith only [h6419, h8005, hlam]
                                        · linarith only [h6418, h8005, hlam]
                                      · have p7969_0 := h7969c.1
                                        have p7969_1 := h7969c.2.1
                                        have p7969_2 := h7969c.2.2.1
                                        have p7969_3 := h7969c.2.2.2
                                        linarith only [hlam, p7969_0]
                                    · rcases h3bigk with h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c | h8009c
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h6419, h7881, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8009_1]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h4, hlam, p8009_1]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h6419, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8009_1]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h6419, hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h1, hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h7875, hlam, p8009_1]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h1, h6419, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8009_1]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h7882, hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        rcases p8009_3 (m.d 0 3) (by simp) with h8020 | h8020
                                        · linarith only [h4, h8020, hlam]
                                        · rcases p8009_3 (m.d 1 3) (by simp) with h8022 | h8022
                                          · linarith only [h7875, h8022, hlam]
                                          · rcases p8009_3 (m.d 2 3) (by simp) with h8024 | h8024
                                            · rcases p8009_3 (m.d 3 4) (by simp) with h8025 | h8025
                                              · linarith only [h7886, h8025, hlam]
                                              · rcases p8009_3 (m.d 3 5) (by simp) with h8027 | h8027
                                                · linarith only [h7887, h8027, hlam]
                                                · linarith only [h6419, h8027, hlam]
                                            · linarith only [h4, h8024, hlam]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        rcases p8009_3 (m.d 0 3) (by simp) with h8031 | h8031
                                        · linarith only [h4, h8031, hlam]
                                        · linarith only [h1, h8031, hlam]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h6418, h6419, h7886, h7888, h7889, hlam, p8009_2]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h1, h6419, h7881, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8009_1]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h6418, hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h7881, hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h7886, hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h7889, hlam, p8009_1]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h1, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8009_1]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8009_1]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [h7887, hlam, p8009_0]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        rcases p8009_3 (m.d 0 3) (by simp) with h8045 | h8045
                                        · linarith only [h6419, h8045, hlam]
                                        · linarith only [h6418, h8045, hlam]
                                      · have p8009_0 := h8009c.1
                                        have p8009_1 := h8009c.2.1
                                        have p8009_2 := h8009c.2.2.1
                                        have p8009_3 := h8009c.2.2.2
                                        linarith only [hlam, p8009_0]
                                    · rcases h3bigk with h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c | h8049c
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h6419, h7881, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8049_1]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h4, hlam, p8049_1]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h6419, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8049_1]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h6419, hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h1, hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h7875, hlam, p8049_1]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h1, h6419, h7886, h7888, h7889, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8049_1]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h7882, hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        rcases p8049_3 (m.d 0 3) (by simp) with h8060 | h8060
                                        · linarith only [h4, h8060, hlam]
                                        · rcases p8049_3 (m.d 1 3) (by simp) with h8062 | h8062
                                          · linarith only [h7875, h8062, hlam]
                                          · rcases p8049_3 (m.d 2 3) (by simp) with h8064 | h8064
                                            · rcases p8049_3 (m.d 3 4) (by simp) with h8065 | h8065
                                              · linarith only [h7886, h8065, hlam]
                                              · rcases p8049_3 (m.d 3 5) (by simp) with h8067 | h8067
                                                · linarith only [h7887, h8067, hlam]
                                                · linarith only [h6419, h8067, hlam]
                                            · linarith only [h4, h8064, hlam]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        rcases p8049_3 (m.d 0 3) (by simp) with h8071 | h8071
                                        · linarith only [h4, h8071, hlam]
                                        · linarith only [h1, h8071, hlam]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h6418, h6419, h7886, h7888, h7889, hlam, p8049_2]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h1, h6419, h7881, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8049_1]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h6418, hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h7881, hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h7886, hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h7889, hlam, p8049_1]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h1, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8049_1]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8049_1]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [h7887, hlam, p8049_0]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        rcases p8049_3 (m.d 0 3) (by simp) with h8085 | h8085
                                        · linarith only [h6419, h8085, hlam]
                                        · linarith only [h6418, h8085, hlam]
                                      · have p8049_0 := h8049c.1
                                        have p8049_1 := h8049c.2.1
                                        have p8049_2 := h8049c.2.2.1
                                        have p8049_3 := h8049c.2.2.2
                                        linarith only [hlam, p8049_0]
                          · linarith only [h7918, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h0, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h7875, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h7877, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h7879, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h1, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h1, h6419, h7886, h7888, h7889, hc12, hc23, hlam, hphi, p7891_1]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h1, h6419, h7877, h7886, h7888, h7889, hc12, hc23, hlam, hphi, p7891_1]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h7882, hlam, p7891_1]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h2, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h2, h6418, h6419, h7886, h7888, h7889, hc12, hc23, hlam, hphi, p7891_1]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h7881, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h7884, hlam, p7891_1]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h3, hlam, p7891_0]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h3, h6419, h7886, h7888, h7889, hc12, hc23, hlam, hphi, p7891_1]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h3, h6419, h7875, h7886, h7888, h7889, hc12, hc23, hlam, hphi, p7891_1]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [h3, h6419, h7877, h7886, h7888, h7889, hc12, hc23, hlam, hphi, p7891_1]
                        · have p7891_0 := h7891c.1
                          have p7891_1 := h7891c.2.1
                          have p7891_2 := h7891c.2.2.1
                          have p7891_3 := h7891c.2.2.2
                          linarith only [hlam, p7891_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8110 | h8110
                      · linarith only [h0, h5543, h7881, h7888, h8110, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h1bigk with h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          rcases p8112_3 (m.d 0 1) (by simp) with h8114 | h8114
                          · rcases p8112_3 (m.d 1 2) (by simp) with h8115 | h8115
                            · linarith only [h8115, hlam, p8112_0]
                            · rcases p8112_3 (m.d 1 3) (by simp) with h8117 | h8117
                              · linarith only [h1, h8117, hlam]
                              · linarith only [h7875, h8117, hlam]
                          · linarith only [h8114, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          rcases p8112_3 (m.d 0 1) (by simp) with h8121 | h8121
                          · rcases p8112_3 (m.d 1 2) (by simp) with h8122 | h8122
                            · linarith only [h0, h8122, hlam]
                            · rcases p8112_3 (m.d 1 3) (by simp) with h8124 | h8124
                              · linarith only [h8124, hlam, p8112_0]
                              · rcases p8112_3 (m.d 1 4) (by simp) with h8126 | h8126
                                · linarith only [h2, h8126, hlam]
                                · rcases p8112_3 (m.d 1 5) (by simp) with h8128 | h8128
                                  · linarith only [h3, h8128, hlam]
                                  · linarith only [h7882, h8128, hlam]
                          · linarith only [h8121, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          rcases p8112_3 (m.d 0 1) (by simp) with h8132 | h8132
                          · rcases p8112_3 (m.d 1 2) (by simp) with h8133 | h8133
                            · linarith only [h0, h8133, hlam]
                            · rcases p8112_3 (m.d 1 3) (by simp) with h8135 | h8135
                              · linarith only [h1, h8135, hlam]
                              · linarith only [h7881, h8135, hlam]
                          · linarith only [h8132, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          rcases p8112_3 (m.d 0 1) (by simp) with h8139 | h8139
                          · rcases p8112_3 (m.d 1 2) (by simp) with h8140 | h8140
                            · linarith only [h0, h8140, hlam]
                            · rcases p8112_3 (m.d 1 3) (by simp) with h8142 | h8142
                              · linarith only [h1, h8142, hlam]
                              · rcases p8112_3 (m.d 1 4) (by simp) with h8144 | h8144
                                · linarith only [h2, h8144, hlam]
                                · rcases p8112_3 (m.d 1 5) (by simp) with h8146 | h8146
                                  · linarith only [h8146, hlam, p8112_0]
                                  · rcases h1emax with h8148 | h8148 | h8148 | h8148 | h8148
                                    · linarith only [h8148, hlam, hphi, ht01, ht0b, ht5b, p8112_1, u5ehi1]
                                    · rcases h3bigk with h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c | h8150c
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h6419, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8150_1]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h4, hlam, p8150_1]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h6419, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8150_1]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h6419, hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h1, hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h7875, hlam, p8150_1]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h7882, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8112_1, p8150_1]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h7882, hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        rcases p8150_3 (m.d 0 3) (by simp) with h8161 | h8161
                                        · linarith only [h4, h8161, hlam]
                                        · rcases p8150_3 (m.d 1 3) (by simp) with h8163 | h8163
                                          · linarith only [h7875, h8163, hlam]
                                          · rcases p8150_3 (m.d 2 3) (by simp) with h8165 | h8165
                                            · rcases p8150_3 (m.d 3 4) (by simp) with h8166 | h8166
                                              · linarith only [h7886, h8166, hlam]
                                              · rcases p8150_3 (m.d 3 5) (by simp) with h8168 | h8168
                                                · linarith only [h7887, h8168, hlam]
                                                · linarith only [h6419, h8168, hlam]
                                            · linarith only [h4, h8165, hlam]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        rcases p8150_3 (m.d 0 3) (by simp) with h8172 | h8172
                                        · linarith only [h4, h8172, hlam]
                                        · linarith only [h1, h8172, hlam]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h6418, h6419, h7887, hlam, p8150_2]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h2, h6418, h6419, h7877, hc12, hc23, hlam, hphi, p8150_1]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h6418, hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h7881, hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h7886, hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h8110, hlam, p8150_1]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h1, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8150_1]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8150_1]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [h7887, hlam, p8150_0]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        rcases p8150_3 (m.d 0 3) (by simp) with h8186 | h8186
                                        · linarith only [h6419, h8186, hlam]
                                        · linarith only [h6418, h8186, hlam]
                                      · have p8150_0 := h8150c.1
                                        have p8150_1 := h8150c.2.1
                                        have p8150_2 := h8150c.2.2.1
                                        have p8150_3 := h8150c.2.2.2
                                        linarith only [hlam, p8150_0]
                                    · rcases h3bigk with h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h6419, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8190_1]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h4, hlam, p8190_1]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h6419, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8190_1]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h6419, hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h1, hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h7875, hlam, p8190_1]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h1, h6419, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8190_1]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h7882, hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        rcases p8190_3 (m.d 0 3) (by simp) with h8201 | h8201
                                        · linarith only [h4, h8201, hlam]
                                        · rcases p8190_3 (m.d 1 3) (by simp) with h8203 | h8203
                                          · linarith only [h7875, h8203, hlam]
                                          · rcases p8190_3 (m.d 2 3) (by simp) with h8205 | h8205
                                            · rcases p8190_3 (m.d 3 4) (by simp) with h8206 | h8206
                                              · linarith only [h7886, h8206, hlam]
                                              · rcases p8190_3 (m.d 3 5) (by simp) with h8208 | h8208
                                                · linarith only [h7887, h8208, hlam]
                                                · linarith only [h6419, h8208, hlam]
                                            · linarith only [h4, h8205, hlam]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        rcases p8190_3 (m.d 0 3) (by simp) with h8212 | h8212
                                        · linarith only [h4, h8212, hlam]
                                        · linarith only [h1, h8212, hlam]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h6418, h6419, h7887, hlam, p8190_2]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h0, h4, h6419, hc12, hc23, hlam, hphi, p8190_1]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h6418, hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h7881, hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h7886, hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h8110, hlam, p8190_1]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h1, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8190_1]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8190_1]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [h7887, hlam, p8190_0]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        rcases p8190_3 (m.d 0 3) (by simp) with h8226 | h8226
                                        · linarith only [h6419, h8226, hlam]
                                        · linarith only [h6418, h8226, hlam]
                                      · have p8190_0 := h8190c.1
                                        have p8190_1 := h8190c.2.1
                                        have p8190_2 := h8190c.2.2.1
                                        have p8190_3 := h8190c.2.2.2
                                        linarith only [hlam, p8190_0]
                                    · rcases h3bigk with h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c | h8230c
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h6419, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8230_1]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h4, hlam, p8230_1]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h6419, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8230_1]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h6419, hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h1, hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h7875, hlam, p8230_1]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h1, h6419, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8230_1]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h7882, hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        rcases p8230_3 (m.d 0 3) (by simp) with h8241 | h8241
                                        · linarith only [h4, h8241, hlam]
                                        · rcases p8230_3 (m.d 1 3) (by simp) with h8243 | h8243
                                          · linarith only [h7875, h8243, hlam]
                                          · rcases p8230_3 (m.d 2 3) (by simp) with h8245 | h8245
                                            · rcases p8230_3 (m.d 3 4) (by simp) with h8246 | h8246
                                              · linarith only [h7886, h8246, hlam]
                                              · rcases p8230_3 (m.d 3 5) (by simp) with h8248 | h8248
                                                · linarith only [h7887, h8248, hlam]
                                                · linarith only [h6419, h8248, hlam]
                                            · linarith only [h4, h8245, hlam]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        rcases p8230_3 (m.d 0 3) (by simp) with h8252 | h8252
                                        · linarith only [h4, h8252, hlam]
                                        · linarith only [h1, h8252, hlam]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h6418, h6419, h7887, hlam, p8230_2]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h0, h4, h6419, hc12, hc23, hlam, hphi, p8230_1]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h6418, hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h7881, hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h7886, hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h8110, hlam, p8230_1]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h1, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8230_1]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8230_1]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [h7887, hlam, p8230_0]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        rcases p8230_3 (m.d 0 3) (by simp) with h8266 | h8266
                                        · linarith only [h6419, h8266, hlam]
                                        · linarith only [h6418, h8266, hlam]
                                      · have p8230_0 := h8230c.1
                                        have p8230_1 := h8230c.2.1
                                        have p8230_2 := h8230c.2.2.1
                                        have p8230_3 := h8230c.2.2.2
                                        linarith only [hlam, p8230_0]
                                    · rcases h3bigk with h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c | h8270c
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h6419, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8270_1]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h4, hlam, p8270_1]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h6419, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8270_1]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h6419, hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h1, hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h7875, hlam, p8270_1]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h1, h6419, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8270_1]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h7882, hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        rcases p8270_3 (m.d 0 3) (by simp) with h8281 | h8281
                                        · linarith only [h4, h8281, hlam]
                                        · rcases p8270_3 (m.d 1 3) (by simp) with h8283 | h8283
                                          · linarith only [h7875, h8283, hlam]
                                          · rcases p8270_3 (m.d 2 3) (by simp) with h8285 | h8285
                                            · rcases p8270_3 (m.d 3 4) (by simp) with h8286 | h8286
                                              · linarith only [h7886, h8286, hlam]
                                              · rcases p8270_3 (m.d 3 5) (by simp) with h8288 | h8288
                                                · linarith only [h7887, h8288, hlam]
                                                · linarith only [h6419, h8288, hlam]
                                            · linarith only [h4, h8285, hlam]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        rcases p8270_3 (m.d 0 3) (by simp) with h8292 | h8292
                                        · linarith only [h4, h8292, hlam]
                                        · linarith only [h1, h8292, hlam]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h6418, h6419, h7887, hlam, p8270_2]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h0, h4, h6419, hc12, hc23, hlam, hphi, p8270_1]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h6418, hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h7881, hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h7886, hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h8110, hlam, p8270_1]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h1, h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8270_1]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h7881, h7887, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8270_1]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [h7887, hlam, p8270_0]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        rcases p8270_3 (m.d 0 3) (by simp) with h8306 | h8306
                                        · linarith only [h6419, h8306, hlam]
                                        · linarith only [h6418, h8306, hlam]
                                      · have p8270_0 := h8270c.1
                                        have p8270_1 := h8270c.2.1
                                        have p8270_2 := h8270c.2.2.1
                                        have p8270_3 := h8270c.2.2.2
                                        linarith only [hlam, p8270_0]
                          · linarith only [h8139, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h0, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h7875, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h7877, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h7879, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h1, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h1, h6419, h7887, hc12, hc23, hlam, hphi, p8112_1]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h1, h6419, h7877, h7887, hc12, hc23, hlam, hphi, p8112_1]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h7882, hlam, p8112_1]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h2, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h2, h6418, h6419, h7887, hc12, hc23, hlam, hphi, p8112_1]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h7881, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h7884, hlam, p8112_1]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h3, hlam, p8112_0]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h3, h6419, h7887, hc12, hc23, hlam, hphi, p8112_1]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h3, h6419, h7875, h7887, hc12, hc23, hlam, hphi, p8112_1]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [h3, h6419, h7877, h7887, hc12, hc23, hlam, hphi, p8112_1]
                        · have p8112_0 := h8112c.1
                          have p8112_1 := h8112c.2.1
                          have p8112_2 := h8112c.2.2.1
                          have p8112_3 := h8112c.2.2.2
                          linarith only [hlam, p8112_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8331 | h8331
                    · linarith only [h2, h7873, h7877, h7886, h7887, h8331, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8333 | h8333
                      · linarith only [h0, h1, h5543, h7881, h8331, h8333, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h1bigk with h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          rcases p8335_3 (m.d 0 1) (by simp) with h8337 | h8337
                          · rcases p8335_3 (m.d 1 2) (by simp) with h8338 | h8338
                            · linarith only [h8338, hlam, p8335_0]
                            · rcases p8335_3 (m.d 1 3) (by simp) with h8340 | h8340
                              · linarith only [h1, h8340, hlam]
                              · linarith only [h7875, h8340, hlam]
                          · linarith only [h8337, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          rcases p8335_3 (m.d 0 1) (by simp) with h8344 | h8344
                          · rcases p8335_3 (m.d 1 2) (by simp) with h8345 | h8345
                            · linarith only [h0, h8345, hlam]
                            · rcases p8335_3 (m.d 1 3) (by simp) with h8347 | h8347
                              · linarith only [h8347, hlam, p8335_0]
                              · rcases p8335_3 (m.d 1 4) (by simp) with h8349 | h8349
                                · linarith only [h2, h8349, hlam]
                                · rcases p8335_3 (m.d 1 5) (by simp) with h8351 | h8351
                                  · linarith only [h3, h8351, hlam]
                                  · linarith only [h7882, h8351, hlam]
                          · linarith only [h8344, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          rcases p8335_3 (m.d 0 1) (by simp) with h8355 | h8355
                          · rcases p8335_3 (m.d 1 2) (by simp) with h8356 | h8356
                            · linarith only [h0, h8356, hlam]
                            · rcases p8335_3 (m.d 1 3) (by simp) with h8358 | h8358
                              · linarith only [h1, h8358, hlam]
                              · linarith only [h7881, h8358, hlam]
                          · linarith only [h8355, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          rcases p8335_3 (m.d 0 1) (by simp) with h8362 | h8362
                          · rcases p8335_3 (m.d 1 2) (by simp) with h8363 | h8363
                            · linarith only [h0, h8363, hlam]
                            · rcases p8335_3 (m.d 1 3) (by simp) with h8365 | h8365
                              · linarith only [h1, h8365, hlam]
                              · rcases p8335_3 (m.d 1 4) (by simp) with h8367 | h8367
                                · linarith only [h2, h8367, hlam]
                                · rcases p8335_3 (m.d 1 5) (by simp) with h8369 | h8369
                                  · linarith only [h8369, hlam, p8335_0]
                                  · rcases h1emax with h8371 | h8371 | h8371 | h8371 | h8371
                                    · linarith only [h7882, h8371, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8335_1]
                                    · rcases h3bigk with h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c | h8373c
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h4, h7881, h7887, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h4, hlam, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h4, h7887, h8333, hc34, hc45, hlam, hphi, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h6419, hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h1, hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h7875, hlam, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h1, h4, h7887, h8333, hc34, hc45, hlam, hphi, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h7882, hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h7887, h8333, hc03, hc45, hlam, hphi, ht34, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h7887, h8333, hc13, hc45, hlam, hphi, ht34, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h7887, h8333, hc34, hc45, hlam, hphi, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h7887, hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h6418, hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h7881, hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h7886, hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [hlam, p8373_0]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h8333, hlam, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h1, h7881, h8333, hc34, hc45, hlam, hphi, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h7881, h8333, hc34, hc45, hlam, hphi, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [h0, h4, h8333, hc12, hc45, hlam, hphi, ht23, ht34, p8373_1]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        rcases p8373_3 (m.d 0 3) (by simp) with h8397 | h8397
                                        · linarith only [h6419, h8397, hlam]
                                        · linarith only [h6418, h8397, hlam]
                                      · have p8373_0 := h8373c.1
                                        have p8373_1 := h8373c.2.1
                                        have p8373_2 := h8373c.2.2.1
                                        have p8373_3 := h8373c.2.2.2
                                        linarith only [hlam, p8373_0]
                                    · rcases h3bigk with h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c | h8401c
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h6419, h7881, h8333, hc34, hc45, hlam, hphi, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h4, hlam, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h6419, h8333, hc34, hc45, hlam, hphi, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h6419, hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h1, hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h7875, hlam, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h1, h6419, h8333, hc34, hc45, hlam, hphi, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h7882, hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h7887, h8333, hc03, hc45, hlam, hphi, ht34, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h7887, h8333, hc13, hc45, hlam, hphi, ht34, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h7887, h8333, hc34, hc45, hlam, hphi, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h7887, hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h6418, hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h7881, hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h7886, hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [hlam, p8401_0]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h8333, hlam, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h1, h7881, h8333, hc34, hc45, hlam, hphi, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h7881, h8333, hc34, hc45, hlam, hphi, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [h0, h4, h8333, hc12, hc45, hlam, hphi, ht23, ht34, p8401_1]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        rcases p8401_3 (m.d 0 3) (by simp) with h8425 | h8425
                                        · linarith only [h6419, h8425, hlam]
                                        · linarith only [h6418, h8425, hlam]
                                      · have p8401_0 := h8401c.1
                                        have p8401_1 := h8401c.2.1
                                        have p8401_2 := h8401c.2.2.1
                                        have p8401_3 := h8401c.2.2.2
                                        linarith only [hlam, p8401_0]
                                    · rcases h3bigk with h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c | h8429c
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h6419, h7881, h8333, hc34, hc45, hlam, hphi, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h4, hlam, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h6419, h8333, hc34, hc45, hlam, hphi, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h6419, hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h1, hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h7875, hlam, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h1, h6419, h8333, hc34, hc45, hlam, hphi, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h7882, hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h7887, h8333, hc03, hc45, hlam, hphi, ht34, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h7887, h8333, hc13, hc45, hlam, hphi, ht34, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h7887, h8333, hc34, hc45, hlam, hphi, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h7887, hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h6418, hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h7881, hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h7886, hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [hlam, p8429_0]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h8333, hlam, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h1, h7881, h8333, hc34, hc45, hlam, hphi, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h7881, h8333, hc34, hc45, hlam, hphi, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [h0, h4, h8333, hc12, hc45, hlam, hphi, ht23, ht34, p8429_1]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        rcases p8429_3 (m.d 0 3) (by simp) with h8453 | h8453
                                        · linarith only [h6419, h8453, hlam]
                                        · linarith only [h6418, h8453, hlam]
                                      · have p8429_0 := h8429c.1
                                        have p8429_1 := h8429c.2.1
                                        have p8429_2 := h8429c.2.2.1
                                        have p8429_3 := h8429c.2.2.2
                                        linarith only [hlam, p8429_0]
                                    · rcases h3bigk with h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c | h8457c
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h6419, h7881, h8333, hc34, hc45, hlam, hphi, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h4, hlam, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h6419, h8333, hc34, hc45, hlam, hphi, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h6419, hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h1, hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h7875, hlam, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h1, h6419, h8333, hc34, hc45, hlam, hphi, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h7882, hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h7887, h8333, hc03, hc45, hlam, hphi, ht34, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h7887, h8333, hc13, hc45, hlam, hphi, ht34, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h7887, h8333, hc34, hc45, hlam, hphi, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h7887, hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h6418, hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h7881, hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h7886, hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [hlam, p8457_0]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h8333, hlam, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h1, h7881, h8333, hc34, hc45, hlam, hphi, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h7881, h8333, hc34, hc45, hlam, hphi, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [h0, h4, h8333, hc12, hc45, hlam, hphi, ht23, ht34, p8457_1]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        rcases p8457_3 (m.d 0 3) (by simp) with h8481 | h8481
                                        · linarith only [h6419, h8481, hlam]
                                        · linarith only [h6418, h8481, hlam]
                                      · have p8457_0 := h8457c.1
                                        have p8457_1 := h8457c.2.1
                                        have p8457_2 := h8457c.2.2.1
                                        have p8457_3 := h8457c.2.2.2
                                        linarith only [hlam, p8457_0]
                          · linarith only [h8362, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h0, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h7875, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h7877, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h7879, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h1, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h1, h6419, h8333, hc12, hc45, hlam, hphi, ht23, ht34, p8335_1]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h1, h6419, h7877, h8333, hc12, hc45, hlam, hphi, ht23, ht34, p8335_1]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h7882, hlam, p8335_1]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h2, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h2, h6418, h6419, h8333, hc12, hc45, hlam, hphi, ht23, ht34, p8335_1]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h7881, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h7884, hlam, p8335_1]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h3, hlam, p8335_0]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          rcases p8335_3 (m.d 0 1) (by simp) with h8502 | h8502
                          · rcases p8335_3 (m.d 1 2) (by simp) with h8503 | h8503
                            · linarith only [h7879, h8503, hlam]
                            · rcases p8335_3 (m.d 1 3) (by simp) with h8505 | h8505
                              · linarith only [h7882, h8505, hlam]
                              · linarith only [h7875, h8505, hlam]
                          · linarith only [h0, h8502, hlam]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [h3, h6343, h7881, h7887, h8333, hc34, hc45, hlam, hphi, p8335_1]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          rcases p8335_3 (m.d 0 1) (by simp) with h8510 | h8510
                          · rcases p8335_3 (m.d 1 2) (by simp) with h8511 | h8511
                            · linarith only [h7879, h8511, hlam]
                            · rcases p8335_3 (m.d 1 3) (by simp) with h8513 | h8513
                              · linarith only [h7882, h8513, hlam]
                              · linarith only [h7881, h8513, hlam]
                          · linarith only [h2, h8510, hlam]
                        · have p8335_0 := h8335c.1
                          have p8335_1 := h8335c.2.1
                          have p8335_2 := h8335c.2.2.1
                          have p8335_3 := h8335c.2.2.2
                          linarith only [hlam, p8335_0]
                · linarith only [h1, h4, h7881, h7886, hlam]
          · linarith only [h6418, h6419, h7881, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 0 3 5 (by decide) (by decide) with h6419 | h6419
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419

end R2N4
