import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3872 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3873 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3874 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h3875 | h3875
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3876 | h3876
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3877 | h3877
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3878 | h3878
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3879 | h3879
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3880 | h3880
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3881 | h3881
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3882 | h3882
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3883 | h3883
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3884 | h3884
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3885 | h3885
                      · linarith only [h0, h3871, h3877, h3882, h3885, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h3871, h3878, h3880, h3884, h3885, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3888 | h3888
                      · linarith only [h0, h3871, h3875, h3884, h3888, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h2bigk with h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c | h3890c
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h0, hlam, p3890_1]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          rcases p3890_3 (m.d 0 2) (by simp) with h3893 | h3893
                          · rcases p3890_3 (m.d 1 2) (by simp) with h3894 | h3894
                            · rcases p3890_3 (m.d 2 3) (by simp) with h3895 | h3895
                              · linarith only [h3895, hlam, p3890_0]
                              · rcases p3890_3 (m.d 2 4) (by simp) with h3897 | h3897
                                · linarith only [h3873, h3897, hlam]
                                · rcases p3890_3 (m.d 2 5) (by simp) with h3899 | h3899
                                  · linarith only [h3874, h3899, hlam]
                                  · rcases h3bigk with h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h0, h3871, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h0, h3871, h3883, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h0, h3871, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h0, h3871, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3871, hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3883, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h0, h3871, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h0, h3871, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3872, hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3877, hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3890_1, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3890_1, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3875, hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3880, hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3882, hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3888, hlam, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3876, hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3881, hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h3883, hlam, p3901_0]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [h0, h3871, h3876, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3901_1]
                                    · have p3901_0 := h3901c.1
                                      have p3901_1 := h3901c.2.1
                                      have p3901_2 := h3901c.2.2.1
                                      have p3901_3 := h3901c.2.2.2
                                      linarith only [hlam, p3901_0]
                            · linarith only [h3877, h3894, hlam]
                          · linarith only [h3893, hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          rcases p3890_3 (m.d 0 2) (by simp) with h3929 | h3929
                          · rcases p3890_3 (m.d 1 2) (by simp) with h3930 | h3930
                            · rcases p3890_3 (m.d 2 3) (by simp) with h3931 | h3931
                              · linarith only [h3872, h3931, hlam]
                              · linarith only [h3882, h3931, hlam]
                            · linarith only [h3878, h3930, hlam]
                          · linarith only [h3929, hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          rcases p3890_3 (m.d 0 2) (by simp) with h3936 | h3936
                          · rcases p3890_3 (m.d 1 2) (by simp) with h3937 | h3937
                            · rcases p3890_3 (m.d 2 3) (by simp) with h3938 | h3938
                              · linarith only [h3872, h3938, hlam]
                              · linarith only [h3883, h3938, hlam]
                            · linarith only [h3879, h3937, hlam]
                          · linarith only [h3936, hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p3890_1, u0ehi1]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          rcases p3890_3 (m.d 0 2) (by simp) with h3945 | h3945
                          · linarith only [h0, h3945, hlam]
                          · linarith only [h3872, h3945, hlam]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          rcases p3890_3 (m.d 0 2) (by simp) with h3948 | h3948
                          · linarith only [h0, h3948, hlam]
                          · linarith only [h3873, h3948, hlam]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          rcases p3890_3 (m.d 0 2) (by simp) with h3951 | h3951
                          · linarith only [h0, h3951, hlam]
                          · linarith only [h3874, h3951, hlam]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h3872, hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h3877, hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h0, h3871, h3877, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3890_1]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h0, h3871, h3877, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3890_1]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h3873, hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h3878, hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h3882, hlam, p3890_1]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h3884, hlam, p3890_1]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h3874, hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h3879, hlam, p3890_0]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h3883, hlam, p3890_1]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [h0, h3871, h3879, h3881, h3882, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3890_1]
                        · have p3890_0 := h3890c.1
                          have p3890_1 := h3890c.2.1
                          have p3890_2 := h3890c.2.2.1
                          have p3890_3 := h3890c.2.2.2
                          linarith only [hlam, p3890_0]
                  · linarith only [h0, h3871, h3881, h3883, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h3871, h3880, h3882, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h3871, h3876, h3880, h3881, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3972 | h3972
              · linarith only [h0, h3871, h3875, h3880, h3972, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3974 | h3974
                · linarith only [h3877, h3880, h3974, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3976 | h3976
                  · linarith only [h0, h3871, h3875, h3877, h3880, h3972, h3976, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3978 | h3978
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3979 | h3979
                      · rcases h2bigk with h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c | h3980c
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h0, hlam, p3980_1]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          rcases p3980_3 (m.d 0 2) (by simp) with h3983 | h3983
                          · rcases p3980_3 (m.d 1 2) (by simp) with h3984 | h3984
                            · rcases p3980_3 (m.d 2 3) (by simp) with h3985 | h3985
                              · linarith only [h3985, hlam, p3980_0]
                              · rcases p3980_3 (m.d 2 4) (by simp) with h3987 | h3987
                                · linarith only [h3873, h3987, hlam]
                                · linarith only [h3974, h3987, hlam]
                            · linarith only [h3877, h3984, hlam]
                          · linarith only [h3983, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          rcases p3980_3 (m.d 0 2) (by simp) with h3992 | h3992
                          · rcases p3980_3 (m.d 1 2) (by simp) with h3993 | h3993
                            · rcases p3980_3 (m.d 2 3) (by simp) with h3994 | h3994
                              · linarith only [h3872, h3994, hlam]
                              · rcases p3980_3 (m.d 2 4) (by simp) with h3996 | h3996
                                · linarith only [h3996, hlam, p3980_0]
                                · rcases p3980_3 (m.d 2 5) (by simp) with h3998 | h3998
                                  · linarith only [h3874, h3998, hlam]
                                  · rcases h3bigk with h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h0, h3871, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4000_1]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4000_1]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h0, h3871, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4000_1]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h0, h3871, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4000_1]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h3871, hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4000_1]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h3880, hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h3972, hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h3872, hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h3877, hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h3974, hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h3976, hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h3875, hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [hc13, hc34, hlam, hphi, p4000_1]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h0, h3871, h3875, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4000_1]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h0, h3871, h3875, h3972, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4000_1]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h3876, hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [hc13, hc35, hlam, hphi, p4000_1]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h0, h3871, h3876, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4000_1]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [h3979, hlam, p4000_0]
                                    · have p4000_0 := h4000c.1
                                      have p4000_1 := h4000c.2.1
                                      have p4000_2 := h4000c.2.2.1
                                      have p4000_3 := h4000c.2.2.2
                                      linarith only [hlam, p4000_0]
                            · linarith only [h3878, h3993, hlam]
                          · linarith only [h3992, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          rcases p3980_3 (m.d 0 2) (by simp) with h4028 | h4028
                          · rcases p3980_3 (m.d 1 2) (by simp) with h4029 | h4029
                            · rcases p3980_3 (m.d 2 3) (by simp) with h4030 | h4030
                              · linarith only [h3872, h4030, hlam]
                              · rcases p3980_3 (m.d 2 4) (by simp) with h4032 | h4032
                                · linarith only [h3873, h4032, hlam]
                                · linarith only [h3978, h4032, hlam]
                            · linarith only [h3879, h4029, hlam]
                          · linarith only [h4028, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p3980_1, u0ehi1]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h0, h3871, h3875, h3877, h3880, hlam, p3980_2]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          rcases p3980_3 (m.d 0 2) (by simp) with h4040 | h4040
                          · linarith only [h0, h4040, hlam]
                          · linarith only [h3873, h4040, hlam]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          rcases p3980_3 (m.d 0 2) (by simp) with h4043 | h4043
                          · linarith only [h0, h4043, hlam]
                          · linarith only [h3874, h4043, hlam]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h3872, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h3877, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h3974, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h3976, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h3873, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h3878, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h0, h3871, h3875, h3878, h3880, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3980_1]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h0, h3871, h3875, h3878, h3880, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3980_1]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h3874, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h3879, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h0, h3871, h3875, h3879, h3972, h3979, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3980_1]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [h3978, hlam, p3980_0]
                        · have p3980_0 := h3980c.1
                          have p3980_1 := h3980c.2.1
                          have p3980_2 := h3980c.2.2.1
                          have p3980_3 := h3980c.2.2.2
                          linarith only [hlam, p3980_0]
                      · linarith only [h3878, h3880, h3978, h3979, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4062 | h4062
                      · linarith only [h0, h3871, h3875, h3978, h4062, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h2bigk with h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c | h4064c
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h0, hlam, p4064_1]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          rcases p4064_3 (m.d 0 2) (by simp) with h4067 | h4067
                          · rcases p4064_3 (m.d 1 2) (by simp) with h4068 | h4068
                            · rcases p4064_3 (m.d 2 3) (by simp) with h4069 | h4069
                              · linarith only [h4069, hlam, p4064_0]
                              · rcases p4064_3 (m.d 2 4) (by simp) with h4071 | h4071
                                · linarith only [h3873, h4071, hlam]
                                · linarith only [h3974, h4071, hlam]
                            · linarith only [h3877, h4068, hlam]
                          · linarith only [h4067, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          rcases p4064_3 (m.d 0 2) (by simp) with h4076 | h4076
                          · rcases p4064_3 (m.d 1 2) (by simp) with h4077 | h4077
                            · rcases p4064_3 (m.d 2 3) (by simp) with h4078 | h4078
                              · linarith only [h3872, h4078, hlam]
                              · rcases p4064_3 (m.d 2 4) (by simp) with h4080 | h4080
                                · linarith only [h4080, hlam, p4064_0]
                                · rcases p4064_3 (m.d 2 5) (by simp) with h4082 | h4082
                                  · linarith only [h3874, h4082, hlam]
                                  · linarith only [h3978, h4082, hlam]
                            · linarith only [h3878, h4077, hlam]
                          · linarith only [h4076, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          rcases p4064_3 (m.d 0 2) (by simp) with h4087 | h4087
                          · rcases p4064_3 (m.d 1 2) (by simp) with h4088 | h4088
                            · rcases p4064_3 (m.d 2 3) (by simp) with h4089 | h4089
                              · linarith only [h3872, h4089, hlam]
                              · rcases p4064_3 (m.d 2 4) (by simp) with h4091 | h4091
                                · linarith only [h3873, h4091, hlam]
                                · rcases p4064_3 (m.d 2 5) (by simp) with h4093 | h4093
                                  · linarith only [h4093, hlam, p4064_0]
                                  · rcases h3bigk with h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c | h4095c
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h0, h3871, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h0, h3871, h3880, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h0, h3871, h3972, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h3871, hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h3880, hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h3972, hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h3872, hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h3877, hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h3974, hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h3976, hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h3875, hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [hc13, hc34, hlam, hphi, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h0, h3871, h3875, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h4062, hlam, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h3876, hlam, p4095_0]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h3877, hc23, hc35, hlam, hphi, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h0, h3871, h3876, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [h0, h3871, h3876, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4095_1]
                                    · have p4095_0 := h4095c.1
                                      have p4095_1 := h4095c.2.1
                                      have p4095_2 := h4095c.2.2.1
                                      have p4095_3 := h4095c.2.2.2
                                      linarith only [hlam, p4095_0]
                            · linarith only [h3879, h4088, hlam]
                          · linarith only [h4087, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, ht01, p4064_1, u0ehi0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h0, h3871, h3875, h3877, h3880, hlam, p4064_2]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          rcases p4064_3 (m.d 0 2) (by simp) with h4126 | h4126
                          · linarith only [h0, h4126, hlam]
                          · linarith only [h3873, h4126, hlam]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          rcases p4064_3 (m.d 0 2) (by simp) with h4129 | h4129
                          · linarith only [h0, h4129, hlam]
                          · linarith only [h3874, h4129, hlam]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h3872, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h3877, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h3974, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h3976, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h3873, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h3878, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h0, h3871, h3875, h3878, h3880, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4064_1]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h3978, hlam, p4064_1]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h3874, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h3879, hlam, p4064_0]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h0, h3871, h3876, h3879, h3972, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4064_1]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [h0, h3871, h3876, h3879, h3972, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4064_1]
                        · have p4064_0 := h4064c.1
                          have p4064_1 := h4064c.2.1
                          have p4064_2 := h4064c.2.2.1
                          have p4064_3 := h4064c.2.2.2
                          linarith only [hlam, p4064_0]
          · linarith only [h0, h3879, hc25, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h3871, h3875, h3878, hc24, hlam, hphi, ht01, ht12, u0ehi3]
      · linarith only [h0, h3871, h3875, h3877, hc23, hlam, hphi, ht01, ht12, u0ehi3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4150 | h4150
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4151 | h4151
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4152 | h4152
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4153 | h4153
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4154 | h4154
              · linarith only [h3871, h3875, h3876, h4154, hc01, hlam, hphi, u0ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4156 | h4156
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4157 | h4157
                  · linarith only [h0, h3871, h3875, h3876, h4150, h4157, hc12, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4159 | h4159
                    · linarith only [h4156, h4157, h4159, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4161 | h4161
                      · linarith only [h0, h3872, h4156, h4159, h4161, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h2bigk with h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h0, hlam, p4163_1]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          rcases p4163_3 (m.d 0 2) (by simp) with h4166 | h4166
                          · rcases p4163_3 (m.d 1 2) (by simp) with h4167 | h4167
                            · rcases p4163_3 (m.d 2 3) (by simp) with h4168 | h4168
                              · linarith only [h4168, hlam, p4163_0]
                              · rcases p4163_3 (m.d 2 4) (by simp) with h4170 | h4170
                                · linarith only [h3873, h4170, hlam]
                                · rcases p4163_3 (m.d 2 5) (by simp) with h4172 | h4172
                                  · linarith only [h3874, h4172, hlam]
                                  · linarith only [h4157, h4172, hlam]
                            · linarith only [h4150, h4167, hlam]
                          · linarith only [h4166, hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          rcases p4163_3 (m.d 0 2) (by simp) with h4177 | h4177
                          · rcases p4163_3 (m.d 1 2) (by simp) with h4178 | h4178
                            · rcases p4163_3 (m.d 2 3) (by simp) with h4179 | h4179
                              · linarith only [h3872, h4179, hlam]
                              · linarith only [h4156, h4179, hlam]
                            · linarith only [h4151, h4178, hlam]
                          · linarith only [h4177, hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          rcases p4163_3 (m.d 0 2) (by simp) with h4184 | h4184
                          · rcases p4163_3 (m.d 1 2) (by simp) with h4185 | h4185
                            · rcases p4163_3 (m.d 2 3) (by simp) with h4186 | h4186
                              · linarith only [h3872, h4186, hlam]
                              · rcases p4163_3 (m.d 2 4) (by simp) with h4188 | h4188
                                · linarith only [h3873, h4188, hlam]
                                · rcases p4163_3 (m.d 2 5) (by simp) with h4190 | h4190
                                  · linarith only [h4190, hlam, p4163_0]
                                  · rcases h3bigk with h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c | h4192c
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h3876, h4161, hc13, hc45, hlam, hphi, ht34, p4192_1]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h3876, h4161, hc23, hc45, hlam, hphi, ht34, p4192_1]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h3876, h4161, hc34, hc45, hlam, hphi, p4192_1]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h3876, hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h3871, hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4192_1]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h0, h3871, h3875, h3876, h4161, hc12, hc34, hc45, hlam, hphi, ht01, p4192_1, u0ehi3]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h4154, hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h3872, hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h4150, hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h0, h3872, h3875, h3876, h4161, hc12, hc34, hc45, hlam, hphi, ht01, p4192_1, u0ehi3]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h4157, hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h3875, hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h4153, hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h4156, hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [hlam, p4192_0]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h4161, hlam, p4192_1]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h3875, h4161, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p4192_1, u0ehi3]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h4161, hc13, hc45, hlam, hphi, ht34, p4192_1]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h4156, h4161, hc34, hc45, hlam, hphi, p4192_1]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [h4161, hc34, hc45, hlam, hphi, p4192_1]
                                    · have p4192_0 := h4192c.1
                                      have p4192_1 := h4192c.2.1
                                      have p4192_2 := h4192c.2.2.1
                                      have p4192_3 := h4192c.2.2.2
                                      linarith only [hlam, p4192_0]
                            · linarith only [h4152, h4185, hlam]
                          · linarith only [h4184, hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p4163_1, u0ehi1]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          rcases p4163_3 (m.d 0 2) (by simp) with h4222 | h4222
                          · linarith only [h0, h4222, hlam]
                          · linarith only [h3872, h4222, hlam]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          rcases p4163_3 (m.d 0 2) (by simp) with h4225 | h4225
                          · linarith only [h0, h4225, hlam]
                          · linarith only [h3873, h4225, hlam]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          rcases p4163_3 (m.d 0 2) (by simp) with h4228 | h4228
                          · linarith only [h0, h4228, hlam]
                          · linarith only [h3874, h4228, hlam]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h3872, hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h4150, hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h0, h3871, h4150, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4163_1]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h4157, hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h3873, hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h4151, hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h4156, hlam, p4163_1]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h4159, hlam, p4163_1]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h3874, hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h4152, hlam, p4163_0]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [h0, h3874, h3875, h3876, h4156, h4161, hc12, hc34, hc45, hlam, hphi, ht01, p4163_1, u0ehi3]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          rcases p4163_3 (m.d 0 2) (by simp) with h4244 | h4244
                          · rcases p4163_3 (m.d 1 2) (by simp) with h4245 | h4245
                            · rcases p4163_3 (m.d 2 3) (by simp) with h4246 | h4246
                              · linarith only [h4157, h4246, hlam]
                              · linarith only [h4156, h4246, hlam]
                            · linarith only [h4151, h4245, hlam]
                          · linarith only [h3873, h4244, hlam]
                        · have p4163_0 := h4163c.1
                          have p4163_1 := h4163c.2.1
                          have p4163_2 := h4163c.2.2.1
                          have p4163_3 := h4163c.2.2.2
                          linarith only [hlam, p4163_0]
                · linarith only [h3875, h3876, h4156, hc23, hc35, hlam, hphi]
            · linarith only [h3875, h3876, h4153, hc13, hc35, hlam, hphi]
          · linarith only [h0, h3874, h4152, hlam]
        · linarith only [h0, h4151, hc24, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h3871, h3875, h4150, hc23, hlam, hphi, ht01, ht12, u0ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4257 | h4257
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4258 | h4258
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4259 | h4259
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4260 | h4260
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4261 | h4261
            · linarith only [h3875, h4257, h4261, hc13, hlam, hphi, ht01, u0ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4263 | h4263
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4264 | h4264
                · linarith only [h3875, h4257, h4264, hc23, hlam, hphi, ht01, ht12, u0ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4266 | h4266
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4267 | h4267
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4268 | h4268
                      · rcases h2bigk with h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h0, hlam, p4269_1]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          rcases p4269_3 (m.d 0 2) (by simp) with h4272 | h4272
                          · rcases p4269_3 (m.d 1 2) (by simp) with h4273 | h4273
                            · rcases p4269_3 (m.d 2 3) (by simp) with h4274 | h4274
                              · linarith only [h4274, hlam, p4269_0]
                              · rcases p4269_3 (m.d 2 4) (by simp) with h4276 | h4276
                                · linarith only [h3873, h4276, hlam]
                                · linarith only [h4264, h4276, hlam]
                            · linarith only [h4258, h4273, hlam]
                          · linarith only [h4272, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          rcases p4269_3 (m.d 0 2) (by simp) with h4281 | h4281
                          · rcases p4269_3 (m.d 1 2) (by simp) with h4282 | h4282
                            · rcases p4269_3 (m.d 2 3) (by simp) with h4283 | h4283
                              · linarith only [h3872, h4283, hlam]
                              · rcases p4269_3 (m.d 2 4) (by simp) with h4285 | h4285
                                · linarith only [h4285, hlam, p4269_0]
                                · rcases p4269_3 (m.d 2 5) (by simp) with h4287 | h4287
                                  · linarith only [h3874, h4287, hlam]
                                  · rcases h3bigk with h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h3875, hc13, hc34, hlam, hphi, p4289_1]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h3875, hc23, hc34, hlam, hphi, p4289_1]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h3875, hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h3875, h4268, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4289_1]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h3871, hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h4266, h4268, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4289_1]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h4261, hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h0, h3871, h4268, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4289_1]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h3872, hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h4258, hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h4264, hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h0, h3872, h4268, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4289_1]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p4289_1]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [hc13, hc34, hlam, hphi, p4289_1]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p4289_1]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      rcases p4289_3 (m.d 0 3) (by simp) with h4309 | h4309
                                      · linarith only [h3875, h4309, hlam]
                                      · linarith only [h4257, h4309, hlam]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h4257, hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h4263, hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h4266, hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [h4268, hlam, p4289_0]
                                    · have p4289_0 := h4289c.1
                                      have p4289_1 := h4289c.2.1
                                      have p4289_2 := h4289c.2.2.1
                                      have p4289_3 := h4289c.2.2.2
                                      linarith only [hlam, p4289_0]
                            · linarith only [h4259, h4282, hlam]
                          · linarith only [h4281, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          rcases p4269_3 (m.d 0 2) (by simp) with h4319 | h4319
                          · rcases p4269_3 (m.d 1 2) (by simp) with h4320 | h4320
                            · rcases p4269_3 (m.d 2 3) (by simp) with h4321 | h4321
                              · linarith only [h3872, h4321, hlam]
                              · linarith only [h4266, h4321, hlam]
                            · linarith only [h4260, h4320, hlam]
                          · linarith only [h4319, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p4269_1, u0ehi1]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          rcases p4269_3 (m.d 0 2) (by simp) with h4328 | h4328
                          · linarith only [h0, h4328, hlam]
                          · linarith only [h3872, h4328, hlam]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          rcases p4269_3 (m.d 0 2) (by simp) with h4331 | h4331
                          · linarith only [h0, h4331, hlam]
                          · linarith only [h3873, h4331, hlam]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          rcases p4269_3 (m.d 0 2) (by simp) with h4334 | h4334
                          · linarith only [h0, h4334, hlam]
                          · linarith only [h3874, h4334, hlam]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h3872, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h4258, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h4264, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h0, h3871, h4258, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4269_1]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h3873, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h4259, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h0, h3873, h4266, h4268, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4269_1]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          rcases p4269_3 (m.d 0 2) (by simp) with h4346 | h4346
                          · rcases p4269_3 (m.d 1 2) (by simp) with h4347 | h4347
                            · rcases p4269_3 (m.d 2 3) (by simp) with h4348 | h4348
                              · linarith only [h4264, h4348, hlam]
                              · linarith only [h4266, h4348, hlam]
                            · linarith only [h4260, h4347, hlam]
                          · linarith only [h3874, h4346, hlam]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h3874, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h4260, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h4266, hlam, p4269_1]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [h4267, hlam, p4269_0]
                        · have p4269_0 := h4269c.1
                          have p4269_1 := h4269c.2.1
                          have p4269_2 := h4269c.2.2.1
                          have p4269_3 := h4269c.2.2.2
                          linarith only [hlam, p4269_0]
                      · linarith only [h3875, h4268, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                    · linarith only [h4264, h4266, h4267, hlam]
                  · linarith only [h3875, h4257, h4266, hc23, hc34, hlam, hphi]
              · linarith only [h3875, h4257, h4263, hc13, hc34, hlam, hphi]
          · linarith only [h0, h4260, hc25, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h4259, hc24, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h4258, hc23, hlam, hphi, ht01, ht12, u0ehi0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4365 | h4365
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4366 | h4366
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4367 | h4367
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4368 | h4368
            · linarith only [h3871, h3875, h4368, hc01, hlam, hphi, u0ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4370 | h4370
              · linarith only [h0, h3871, h4257, h4370, hc12, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4372 | h4372
                · linarith only [h0, h3871, h3875, h4365, h4372, hc12, hlam, hphi, ht01, u0ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4374 | h4374
                  · linarith only [h0, h3871, h4257, h4365, h4374, hc12, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4376 | h4376
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4377 | h4377
                      · rcases h2bigk with h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c | h4378c
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [h0, hlam, p4378_1]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          rcases p4378_3 (m.d 0 2) (by simp) with h4381 | h4381
                          · rcases p4378_3 (m.d 1 2) (by simp) with h4382 | h4382
                            · rcases p4378_3 (m.d 2 3) (by simp) with h4383 | h4383
                              · linarith only [h4383, hlam, p4378_0]
                              · rcases p4378_3 (m.d 2 4) (by simp) with h4385 | h4385
                                · linarith only [h3873, h4385, hlam]
                                · linarith only [h4372, h4385, hlam]
                            · linarith only [h4365, h4382, hlam]
                          · linarith only [h4381, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          rcases p4378_3 (m.d 0 2) (by simp) with h4390 | h4390
                          · rcases p4378_3 (m.d 1 2) (by simp) with h4391 | h4391
                            · rcases p4378_3 (m.d 2 3) (by simp) with h4392 | h4392
                              · linarith only [h3872, h4392, hlam]
                              · rcases p4378_3 (m.d 2 4) (by simp) with h4394 | h4394
                                · linarith only [h4394, hlam, p4378_0]
                                · rcases p4378_3 (m.d 2 5) (by simp) with h4396 | h4396
                                  · linarith only [h3874, h4396, hlam]
                                  · rcases h3bigk with h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4257, h4377, hc13, hc34, hlam, hphi, p4398_1]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4257, h4377, hc23, hc34, hlam, hphi, p4398_1]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h3875, hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4257, hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h3871, hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4398_1]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4368, hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4370, hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h3872, hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4365, hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4372, hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4374, hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p4398_1]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [hc13, hc34, hlam, hphi, p4398_1]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p4398_1]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4257, hc34, hlam, hphi, ht01, ht12, ht23, p4398_1, u0ehi2]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p4398_1, u0ehi2]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4365, hc23, hc35, hlam, hphi, p4398_1]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [hc23, hc35, hlam, hphi, p4398_1]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [h4377, hlam, p4398_0]
                                    · have p4398_0 := h4398c.1
                                      have p4398_1 := h4398c.2.1
                                      have p4398_2 := h4398c.2.2.1
                                      have p4398_3 := h4398c.2.2.2
                                      linarith only [hlam, p4398_0]
                            · linarith only [h4366, h4391, hlam]
                          · linarith only [h4390, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          rcases p4378_3 (m.d 0 2) (by simp) with h4426 | h4426
                          · rcases p4378_3 (m.d 1 2) (by simp) with h4427 | h4427
                            · rcases p4378_3 (m.d 2 3) (by simp) with h4428 | h4428
                              · linarith only [h3872, h4428, hlam]
                              · rcases p4378_3 (m.d 2 4) (by simp) with h4430 | h4430
                                · linarith only [h3873, h4430, hlam]
                                · linarith only [h4376, h4430, hlam]
                            · linarith only [h4367, h4427, hlam]
                          · linarith only [h4426, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p4378_1, u0ehi1]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          rcases p4378_3 (m.d 0 2) (by simp) with h4437 | h4437
                          · linarith only [h0, h4437, hlam]
                          · linarith only [h3872, h4437, hlam]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          rcases p4378_3 (m.d 0 2) (by simp) with h4440 | h4440
                          · linarith only [h0, h4440, hlam]
                          · linarith only [h3873, h4440, hlam]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          rcases p4378_3 (m.d 0 2) (by simp) with h4443 | h4443
                          · linarith only [h0, h4443, hlam]
                          · linarith only [h3874, h4443, hlam]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [h3872, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [h4365, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [h4372, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [h4374, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [h3873, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [h4366, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          rcases p4378_3 (m.d 0 2) (by simp) with h4453 | h4453
                          · rcases p4378_3 (m.d 1 2) (by simp) with h4454 | h4454
                            · rcases p4378_3 (m.d 2 3) (by simp) with h4455 | h4455
                              · linarith only [h4372, h4455, hlam]
                              · rcases p4378_3 (m.d 2 4) (by simp) with h4457 | h4457
                                · rcases p4378_3 (m.d 2 5) (by simp) with h4458 | h4458
                                  · linarith only [h4376, h4458, hlam]
                                  · linarith only [h4374, h4458, hlam]
                                · linarith only [h4372, h4457, hlam]
                            · linarith only [h4365, h4454, hlam]
                          · linarith only [h3872, h4453, hlam]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          rcases p4378_3 (m.d 0 2) (by simp) with h4465 | h4465
                          · rcases p4378_3 (m.d 1 2) (by simp) with h4466 | h4466
                            · rcases p4378_3 (m.d 2 3) (by simp) with h4467 | h4467
                              · linarith only [h4372, h4467, hlam]
                              · rcases p4378_3 (m.d 2 4) (by simp) with h4469 | h4469
                                · rcases p4378_3 (m.d 2 5) (by simp) with h4470 | h4470
                                  · linarith only [h4376, h4470, hlam]
                                  · rcases h3bigk with h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h0, h3871, h4365, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4472_1]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4472_1]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h3875, hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h4257, hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h3871, hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4472_1]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h4368, hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h4370, hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h3872, hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h4365, hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h4372, hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h4374, hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p4472_1]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [hc13, hc34, hlam, hphi, p4472_1]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p4472_1]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h4257, hc34, hlam, hphi, ht01, ht12, ht23, p4472_1, u0ehi2]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p4472_1, u0ehi2]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h4365, hc23, hc35, hlam, hphi, p4472_1]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [hc23, hc35, hlam, hphi, p4472_1]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [h4377, hlam, p4472_0]
                                    · have p4472_0 := h4472c.1
                                      have p4472_1 := h4472c.2.1
                                      have p4472_2 := h4472c.2.2.1
                                      have p4472_3 := h4472c.2.2.2
                                      linarith only [hlam, p4472_0]
                                · linarith only [h4376, h4469, hlam]
                            · linarith only [h4367, h4466, hlam]
                          · linarith only [h3874, h4465, hlam]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [h3874, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [h4367, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          rcases p4378_3 (m.d 0 2) (by simp) with h4503 | h4503
                          · rcases p4378_3 (m.d 1 2) (by simp) with h4504 | h4504
                            · rcases p4378_3 (m.d 2 3) (by simp) with h4505 | h4505
                              · linarith only [h4374, h4505, hlam]
                              · rcases p4378_3 (m.d 2 4) (by simp) with h4507 | h4507
                                · rcases p4378_3 (m.d 2 5) (by simp) with h4508 | h4508
                                  · rcases h3bigk with h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c | h4509c
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h0, h3871, h4365, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4509_1]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4509_1]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h3875, hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h4257, hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h3871, hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4509_1]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h4368, hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h4370, hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h3872, hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h4365, hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h4372, hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h4374, hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p4509_1]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [hc13, hc34, hlam, hphi, p4509_1]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p4509_1]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h4257, hc34, hlam, hphi, ht01, ht12, ht23, p4509_1, u0ehi2]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p4509_1, u0ehi2]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h4365, hc23, hc35, hlam, hphi, p4509_1]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [hc23, hc35, hlam, hphi, p4509_1]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [h4377, hlam, p4509_0]
                                    · have p4509_0 := h4509c.1
                                      have p4509_1 := h4509c.2.1
                                      have p4509_2 := h4509c.2.2.1
                                      have p4509_3 := h4509c.2.2.2
                                      linarith only [hlam, p4509_0]
                                  · linarith only [h4374, h4508, hlam]
                                · linarith only [h4372, h4507, hlam]
                            · linarith only [h4365, h4504, hlam]
                          · linarith only [h3872, h4503, hlam]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [h4376, hlam, p4378_0]
                        · have p4378_0 := h4378c.1
                          have p4378_1 := h4378c.2.1
                          have p4378_2 := h4378c.2.2.1
                          have p4378_3 := h4378c.2.2.2
                          linarith only [hlam, p4378_0]
                      · linarith only [h3875, h4377, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4542 | h4542
                      · rcases h2bigk with h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h0, hlam, p4543_1]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          rcases p4543_3 (m.d 0 2) (by simp) with h4546 | h4546
                          · rcases p4543_3 (m.d 1 2) (by simp) with h4547 | h4547
                            · rcases p4543_3 (m.d 2 3) (by simp) with h4548 | h4548
                              · linarith only [h4548, hlam, p4543_0]
                              · rcases p4543_3 (m.d 2 4) (by simp) with h4550 | h4550
                                · linarith only [h3873, h4550, hlam]
                                · linarith only [h4372, h4550, hlam]
                            · linarith only [h4365, h4547, hlam]
                          · linarith only [h4546, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          rcases p4543_3 (m.d 0 2) (by simp) with h4555 | h4555
                          · rcases p4543_3 (m.d 1 2) (by simp) with h4556 | h4556
                            · rcases p4543_3 (m.d 2 3) (by simp) with h4557 | h4557
                              · linarith only [h3872, h4557, hlam]
                              · rcases p4543_3 (m.d 2 4) (by simp) with h4559 | h4559
                                · linarith only [h4559, hlam, p4543_0]
                                · rcases p4543_3 (m.d 2 5) (by simp) with h4561 | h4561
                                  · linarith only [h3874, h4561, hlam]
                                  · linarith only [h4376, h4561, hlam]
                            · linarith only [h4366, h4556, hlam]
                          · linarith only [h4555, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          rcases p4543_3 (m.d 0 2) (by simp) with h4566 | h4566
                          · rcases p4543_3 (m.d 1 2) (by simp) with h4567 | h4567
                            · rcases p4543_3 (m.d 2 3) (by simp) with h4568 | h4568
                              · linarith only [h3872, h4568, hlam]
                              · rcases p4543_3 (m.d 2 4) (by simp) with h4570 | h4570
                                · linarith only [h3873, h4570, hlam]
                                · rcases p4543_3 (m.d 2 5) (by simp) with h4572 | h4572
                                  · linarith only [h4572, hlam, p4543_0]
                                  · rcases h3bigk with h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h0, h3871, h4365, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4574_1]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4574_1]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h3875, hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h4257, hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h3871, hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h0, h3871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4574_1]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h4368, hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h4370, hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h3872, hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h4365, hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h4372, hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h4374, hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p4574_1]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [hc13, hc34, hlam, hphi, p4574_1]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p4574_1]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h4257, hc34, hlam, hphi, ht01, ht12, ht23, p4574_1, u0ehi2]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p4574_1, u0ehi2]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h4365, hc23, hc35, hlam, hphi, p4574_1]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [hc23, hc35, hlam, hphi, p4574_1]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [h4542, hlam, p4574_0]
                                    · have p4574_0 := h4574c.1
                                      have p4574_1 := h4574c.2.1
                                      have p4574_2 := h4574c.2.2.1
                                      have p4574_3 := h4574c.2.2.2
                                      linarith only [hlam, p4574_0]
                            · linarith only [h4367, h4567, hlam]
                          · linarith only [h4566, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p4543_1, u0ehi1]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          rcases p4543_3 (m.d 0 2) (by simp) with h4604 | h4604
                          · linarith only [h0, h4604, hlam]
                          · linarith only [h3872, h4604, hlam]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          rcases p4543_3 (m.d 0 2) (by simp) with h4607 | h4607
                          · linarith only [h0, h4607, hlam]
                          · linarith only [h3873, h4607, hlam]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          rcases p4543_3 (m.d 0 2) (by simp) with h4610 | h4610
                          · linarith only [h0, h4610, hlam]
                          · linarith only [h3874, h4610, hlam]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h3872, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h4365, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h4372, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h4374, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h3873, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h4366, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h4376, h4542, hc23, hc34, hlam, hphi, p4543_1]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h4376, hlam, p4543_1]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h3874, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h4367, hlam, p4543_0]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h4376, h4542, hc23, hc34, hlam, hphi, p4543_1]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [h4372, h4376, h4542, hc23, hc34, hlam, hphi, p4543_1]
                        · have p4543_0 := h4543c.1
                          have p4543_1 := h4543c.2.1
                          have p4543_2 := h4543c.2.2.1
                          have p4543_3 := h4543c.2.2.2
                          linarith only [hlam, p4543_0]
                      · linarith only [h3875, h4542, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
          · linarith only [h0, h3871, h3874, h4367, hc02, hlam, hphi, u0ehi2]
        · linarith only [h0, h3871, h4366, hc24, hlam, hphi, ht01, ht12, u0ehi2]
      · linarith only [h0, h3871, h4365, hc23, hlam, hphi, ht01, ht12, u0ehi2]

end R2N4
