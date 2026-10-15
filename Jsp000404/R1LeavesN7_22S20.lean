import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5526000 in
set_option maxHeartbeats 5526000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s5_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3977 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4846 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h4847 | h4847
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4848 | h4848
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4849 | h4849
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4850 | h4850
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4851 | h4851
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4852 | h4852
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4853 | h4853
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4854 | h4854
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4855 | h4855
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4856 | h4856
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4857 | h4857
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4858 | h4858
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4859 | h4859
                          · linarith only [h3977, h4846, h4854, h4859, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4861 | h4861
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4862 | h4862
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4863 | h4863
                                · linarith only [h4855, h4859, h4863, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4865 | h4865
                                  · linarith only [h4855, h4859, h4861, h4865, hlam]
                                  · rcases h2bigk with h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c | h4867c
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h0, hlam, p4867_1]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4862, hc02, hlam, hphi, ht0b, ht5b, p4867_1, u5ehi3]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      rcases p4867_3 (m.d 0 2) (by simp) with h4871 | h4871
                                      · rcases p4867_3 (m.d 1 2) (by simp) with h4872 | h4872
                                        · rcases p4867_3 (m.d 2 3) (by simp) with h4873 | h4873
                                          · linarith only [h4848, h4873, hlam]
                                          · linarith only [h4861, h4873, hlam]
                                        · linarith only [h4855, h4872, hlam]
                                      · linarith only [h4871, hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      rcases p4867_3 (m.d 0 2) (by simp) with h4878 | h4878
                                      · rcases p4867_3 (m.d 1 2) (by simp) with h4879 | h4879
                                        · rcases p4867_3 (m.d 2 3) (by simp) with h4880 | h4880
                                          · linarith only [h4848, h4880, hlam]
                                          · linarith only [h4862, h4880, hlam]
                                        · linarith only [h4856, h4879, hlam]
                                      · linarith only [h4878, hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p4867_1, u0ehi1]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4862, hc12, hlam, hphi, ht01, ht0b, ht5b, p4867_1, u5ehi3]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h3977, h4846, h4853, h4854, h4855, h4859, hlam, p4867_2]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      rcases p4867_3 (m.d 0 2) (by simp) with h4889 | h4889
                                      · linarith only [h0, h4889, hlam]
                                      · linarith only [h4850, h4889, hlam]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4848, hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4854, hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      rcases p4867_3 (m.d 0 2) (by simp) with h4895 | h4895
                                      · rcases p4867_3 (m.d 1 2) (by simp) with h4896 | h4896
                                        · rcases p4867_3 (m.d 2 3) (by simp) with h4897 | h4897
                                          · rcases p4867_3 (m.d 2 4) (by simp) with h4898 | h4898
                                            · linarith only [h4861, h4898, hlam]
                                            · rcases p4867_3 (m.d 2 5) (by simp) with h4900 | h4900
                                              · linarith only [h4862, h4900, hlam]
                                              · linarith only [h4863, h4900, hlam]
                                          · linarith only [h4861, h4897, hlam]
                                        · linarith only [h4855, h4896, hlam]
                                      · linarith only [h4849, h4895, hlam]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4848, hc02, hlam, hphi, ht0b, ht5b, p4867_1, u5ehi2]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4849, hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4855, hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4861, hlam, p4867_1]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4863, hlam, p4867_1]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4850, hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4856, hlam, p4867_0]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h4862, hlam, p4867_1]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [h3977, h4846, h4853, h4854, h4856, h4859, h4861, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4867_1]
                                    · have p4867_0 := h4867c.1
                                      have p4867_1 := h4867c.2.1
                                      have p4867_2 := h4867c.2.2.1
                                      have p4867_3 := h4867c.2.2.2
                                      linarith only [hlam, p4867_0]
                              · linarith only [h3977, h4846, h4853, h4854, h4858, h4859, h4861, h4862, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h3977, h4846, h4853, h4854, h4857, h4859, h4861, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h3977, h4846, h4853, h4858, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h3977, h4846, h4853, h4857, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · linarith only [h0, h4846, h4853, h4856, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h3977, h4846, h4853, h4854, h4855, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h4846, h4853, h4854, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4924 | h4924
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4925 | h4925
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4926 | h4926
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4927 | h4927
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4928 | h4928
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4929 | h4929
                          · linarith only [h3977, h4846, h4853, h4924, h4929, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4931 | h4931
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4932 | h4932
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4933 | h4933
                                · linarith only [h3977, h4847, h4853, h4924, h4925, h4929, h4933, hc12, hlam, hphi, ht01, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4935 | h4935
                                  · linarith only [h4848, h4853, h4931, h4935, hc02, hlam, hphi, u0ehi3]
                                  · rcases h2bigk with h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h0, hlam, p4937_1]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h0, h4932, hc12, hlam, hphi, ht01, ht0b, ht5b, p4937_1, u5ehi3]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      rcases p4937_3 (m.d 0 2) (by simp) with h4941 | h4941
                                      · rcases p4937_3 (m.d 1 2) (by simp) with h4942 | h4942
                                        · rcases p4937_3 (m.d 2 3) (by simp) with h4943 | h4943
                                          · linarith only [h4848, h4943, hlam]
                                          · linarith only [h4931, h4943, hlam]
                                        · linarith only [h4925, h4942, hlam]
                                      · linarith only [h4941, hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      rcases p4937_3 (m.d 0 2) (by simp) with h4948 | h4948
                                      · rcases p4937_3 (m.d 1 2) (by simp) with h4949 | h4949
                                        · rcases p4937_3 (m.d 2 3) (by simp) with h4950 | h4950
                                          · linarith only [h4848, h4950, hlam]
                                          · linarith only [h4932, h4950, hlam]
                                        · linarith only [h4926, h4949, hlam]
                                      · linarith only [h4948, hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p4937_1, u0ehi1]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4932, hc12, hlam, hphi, ht01, ht0b, ht5b, p4937_1, u5ehi3]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      rcases p4937_3 (m.d 0 2) (by simp) with h4958 | h4958
                                      · linarith only [h0, h4958, hlam]
                                      · linarith only [h4849, h4958, hlam]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      rcases p4937_3 (m.d 0 2) (by simp) with h4961 | h4961
                                      · linarith only [h0, h4961, hlam]
                                      · linarith only [h4850, h4961, hlam]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4848, hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4924, hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      rcases p4937_3 (m.d 0 2) (by simp) with h4967 | h4967
                                      · rcases p4937_3 (m.d 1 2) (by simp) with h4968 | h4968
                                        · rcases p4937_3 (m.d 2 3) (by simp) with h4969 | h4969
                                          · rcases p4937_3 (m.d 2 4) (by simp) with h4970 | h4970
                                            · linarith only [h4931, h4970, hlam]
                                            · rcases p4937_3 (m.d 2 5) (by simp) with h4972 | h4972
                                              · linarith only [h4932, h4972, hlam]
                                              · linarith only [h4933, h4972, hlam]
                                          · linarith only [h4931, h4969, hlam]
                                        · linarith only [h4925, h4968, hlam]
                                      · linarith only [h4849, h4967, hlam]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4848, hc02, hlam, hphi, ht0b, ht5b, p4937_1, u5ehi2]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4849, hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4925, hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4931, hlam, p4937_1]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4933, hlam, p4937_1]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4850, hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4926, hlam, p4937_0]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h4932, hlam, p4937_1]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [h3977, h4847, h4924, h4926, h4931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4937_1]
                                    · have p4937_0 := h4937c.1
                                      have p4937_1 := h4937c.2.1
                                      have p4937_2 := h4937c.2.2.1
                                      have p4937_3 := h4937c.2.2.2
                                      linarith only [hlam, p4937_0]
                              · linarith only [h3977, h4847, h4924, h4928, h4931, h4932, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4990 | h4990
                              · linarith only [h3977, h4851, h4924, h4931, h4990, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4992 | h4992
                                · linarith only [h3977, h4847, h4853, h4924, h4927, h4929, h4931, h4992, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4994 | h4994
                                  · linarith only [h3977, h4847, h4853, h4924, h4927, h4929, h4994, hc12, hlam, hphi, ht01, u0ehi3]
                                  · rcases h2bigk with h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c | h4996c
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h0, hlam, p4996_1]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      rcases p4996_3 (m.d 0 2) (by simp) with h4999 | h4999
                                      · rcases p4996_3 (m.d 1 2) (by simp) with h5000 | h5000
                                        · rcases p4996_3 (m.d 2 3) (by simp) with h5001 | h5001
                                          · linarith only [h5001, hlam, p4996_0]
                                          · rcases p4996_3 (m.d 2 4) (by simp) with h5003 | h5003
                                            · linarith only [h4849, h5003, hlam]
                                            · linarith only [h4931, h5003, hlam]
                                        · linarith only [h4924, h5000, hlam]
                                      · linarith only [h4999, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      rcases p4996_3 (m.d 0 2) (by simp) with h5008 | h5008
                                      · rcases p4996_3 (m.d 1 2) (by simp) with h5009 | h5009
                                        · rcases p4996_3 (m.d 2 3) (by simp) with h5010 | h5010
                                          · linarith only [h4848, h5010, hlam]
                                          · rcases p4996_3 (m.d 2 4) (by simp) with h5012 | h5012
                                            · linarith only [h5012, hlam, p4996_0]
                                            · rcases p4996_3 (m.d 2 5) (by simp) with h5014 | h5014
                                              · linarith only [h4850, h5014, hlam]
                                              · linarith only [h4992, h5014, hlam]
                                        · linarith only [h4925, h5009, hlam]
                                      · linarith only [h5008, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      rcases p4996_3 (m.d 0 2) (by simp) with h5019 | h5019
                                      · rcases p4996_3 (m.d 1 2) (by simp) with h5020 | h5020
                                        · rcases p4996_3 (m.d 2 3) (by simp) with h5021 | h5021
                                          · linarith only [h4848, h5021, hlam]
                                          · rcases p4996_3 (m.d 2 4) (by simp) with h5023 | h5023
                                            · linarith only [h4849, h5023, hlam]
                                            · rcases p4996_3 (m.d 2 5) (by simp) with h5025 | h5025
                                              · linarith only [h5025, hlam, p4996_0]
                                              · rcases h3bigk with h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c | h5027c
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h3977, hlam, p5027_1]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  rcases p5027_3 (m.d 0 3) (by simp) with h5030 | h5030
                                                  · rcases p5027_3 (m.d 1 3) (by simp) with h5031 | h5031
                                                    · rcases p5027_3 (m.d 2 3) (by simp) with h5032 | h5032
                                                      · linarith only [h4848, h5032, hlam]
                                                      · rcases p5027_3 (m.d 3 4) (by simp) with h5034 | h5034
                                                        · linarith only [h4851, h5034, hlam]
                                                        · linarith only [h4931, h5034, hlam]
                                                    · linarith only [h4924, h5031, hlam]
                                                  · linarith only [h4848, h5030, hlam]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  rcases p5027_3 (m.d 0 3) (by simp) with h5039 | h5039
                                                  · rcases p5027_3 (m.d 1 3) (by simp) with h5040 | h5040
                                                    · rcases p5027_3 (m.d 2 3) (by simp) with h5041 | h5041
                                                      · linarith only [h4848, h5041, hlam]
                                                      · rcases p5027_3 (m.d 3 4) (by simp) with h5043 | h5043
                                                        · linarith only [h5043, hlam, p5027_0]
                                                        · rcases p5027_3 (m.d 3 5) (by simp) with h5045 | h5045
                                                          · linarith only [h4852, h5045, hlam]
                                                          · linarith only [h4994, h5045, hlam]
                                                    · linarith only [h4927, h5040, hlam]
                                                  · linarith only [h5039, hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  rcases p5027_3 (m.d 0 3) (by simp) with h5050 | h5050
                                                  · rcases p5027_3 (m.d 1 3) (by simp) with h5051 | h5051
                                                    · rcases p5027_3 (m.d 2 3) (by simp) with h5052 | h5052
                                                      · linarith only [h4848, h5052, hlam]
                                                      · rcases p5027_3 (m.d 3 4) (by simp) with h5054 | h5054
                                                        · linarith only [h4851, h5054, hlam]
                                                        · rcases p5027_3 (m.d 3 5) (by simp) with h5056 | h5056
                                                          · linarith only [h5056, hlam, p5027_0]
                                                          · rcases h5bigk with h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [hlam, p5058_0]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h3977, h4847, h4924, hc12, hlam, hphi, ht01, ht0b, ht5b, p5058_1, u5ehi1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h3977, h4847, h4924, hc12, hlam, hphi, ht01, ht0b, ht5b, p5058_1, u5ehi2]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h3977, h4847, h4924, h4931, h4994, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4853, hlam, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4847, hlam, p5058_0]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [hlam, p5058_0]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h3977, h4847, h4924, hc12, hlam, hphi, ht01, ht0b, ht5b, p5058_1, u5ehi2]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h3977, h4847, h4924, h4931, h4994, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4929, hlam, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4850, hlam, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4926, hlam, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [hlam, p5058_0]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4990, hlam, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4992, hlam, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4852, hlam, p5058_0]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4928, hlam, p5058_0]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4848, hc02, hlam, hphi, ht0b, ht5b, p5027_1, p5058_1, u5ehi2]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [hlam, p5058_0]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4994, hlam, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p5058_1, u0ehi4]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4927, h4929, h4931, hc23, hc45, hlam, hphi, ht34, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              rcases p5058_3 (m.d 0 5) (by simp) with h5081 | h5081
                                                              · linarith only [h4853, h5081, hlam]
                                                              · linarith only [h4850, h5081, hlam]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [h4990, hc23, hc45, hlam, hphi, ht34, p5058_1]
                                                            · have p5058_0 := h5058c.1
                                                              have p5058_1 := h5058c.2.1
                                                              have p5058_2 := h5058c.2.2.1
                                                              have p5058_3 := h5058c.2.2.2
                                                              linarith only [hlam, p5058_0]
                                                    · linarith only [h4928, h5051, hlam]
                                                  · linarith only [h5050, hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h4924, hc12, hlam, hphi, ht01, p5027_1, u0ehi2]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h3977, h4847, h4927, h4929, h4931, hlam, p5027_2]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  rcases p5027_3 (m.d 0 3) (by simp) with h5091 | h5091
                                                  · linarith only [h3977, h5091, hlam]
                                                  · linarith only [h4851, h5091, hlam]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  rcases p5027_3 (m.d 0 3) (by simp) with h5094 | h5094
                                                  · linarith only [h3977, h5094, hlam]
                                                  · linarith only [h4852, h5094, hlam]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h4848, hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h4924, hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h4931, hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h4990, hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h4851, hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h4927, hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h3977, h4847, h4924, h4927, h4929, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5027_1]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h4994, hlam, p5027_1]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h4852, hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h4928, hlam, p5027_0]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h3977, h4847, h4924, h4928, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5027_1]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [h3977, h4847, h4924, h4928, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5027_1]
                                                · have p5027_0 := h5027c.1
                                                  have p5027_1 := h5027c.2.1
                                                  have p5027_2 := h5027c.2.2.1
                                                  have p5027_3 := h5027c.2.2.2
                                                  linarith only [hlam, p5027_0]
                                        · linarith only [h4926, h5020, hlam]
                                      · linarith only [h5019, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p4996_1, u0ehi1]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h3977, h4847, h4924, h4927, h4929, h4931, hlam, p4996_2]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      rcases p4996_3 (m.d 0 2) (by simp) with h5117 | h5117
                                      · linarith only [h0, h5117, hlam]
                                      · linarith only [h4849, h5117, hlam]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      rcases p4996_3 (m.d 0 2) (by simp) with h5120 | h5120
                                      · linarith only [h0, h5120, hlam]
                                      · linarith only [h4850, h5120, hlam]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h4848, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h4924, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h4931, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h4990, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h4849, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h4925, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h4849, h4853, hc23, hc45, hlam, hphi, ht34, p4996_1]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h4992, hlam, p4996_1]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h4850, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h4926, hlam, p4996_0]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h3977, h4847, h4924, h4926, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4996_1]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [h3977, h4847, h4924, h4928, h4990, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4996_1]
                                    · have p4996_0 := h4996c.1
                                      have p4996_1 := h4996c.2.1
                                      have p4996_2 := h4996c.2.2.1
                                      have p4996_3 := h4996c.2.2.2
                                      linarith only [hlam, p4996_0]
                        · linarith only [h3977, h4847, h4928, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h3977, h4847, h4927, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h3977, h4847, h4853, h4924, h4926, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h3977, h4847, h4853, h4924, h4925, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                · linarith only [h0, h4847, h4853, h4924, hc23, hlam, hphi, ht01, ht12, u0ehi3]
            · linarith only [h3977, h4847, h4852, hlam]
          · linarith only [h3977, h4846, h4851, hlam]
        · linarith only [h0, h4847, h4850, hlam]
      · linarith only [h3977, h4846, h4848, h4849, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5147 | h5147
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5148 | h5148
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5149 | h5149
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5150 | h5150
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5151 | h5151
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5152 | h5152
                · linarith only [h4848, h5148, h5152, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h4846, h5151, h5152, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5155 | h5155
                · linarith only [h4848, h5148, h5155, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h4847, h5151, h5155, hc23, hlam, hphi, ht01, ht12, u0ehi3]
            · linarith only [h0, h4847, h4848, h5150, hlam]
          · linarith only [h0, h4846, h4848, h5149, hlam]
        · linarith only [h0, h4847, h5148, hlam]
      · linarith only [h0, h4846, h5147, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h5162 | h5162
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5163 | h5163
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5164 | h5164
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5165 | h5165
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5166 | h5166
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5167 | h5167
              · linarith only [h4846, h4847, h5167, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5169 | h5169
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5170 | h5170
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5171 | h5171
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5172 | h5172
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5173 | h5173
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5174 | h5174
                          · linarith only [h5167, h5174, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5176 | h5176
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5177 | h5177
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5178 | h5178
                                · linarith only [h4846, h4847, h5170, h5174, h5178, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5180 | h5180
                                  · linarith only [h4846, h4847, h5170, h5174, h5176, h5180, hlam]
                                  · rcases h2bigk with h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c | h5182c
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h0, hlam, p5182_1]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5177, hc02, hlam, hphi, ht0b, ht5b, p5182_1, u5ehi3]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      rcases p5182_3 (m.d 0 2) (by simp) with h5186 | h5186
                                      · rcases p5182_3 (m.d 1 2) (by simp) with h5187 | h5187
                                        · rcases p5182_3 (m.d 2 3) (by simp) with h5188 | h5188
                                          · linarith only [h5162, h5188, hlam]
                                          · linarith only [h5176, h5188, hlam]
                                        · linarith only [h5170, h5187, hlam]
                                      · linarith only [h5186, hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      rcases p5182_3 (m.d 0 2) (by simp) with h5193 | h5193
                                      · rcases p5182_3 (m.d 1 2) (by simp) with h5194 | h5194
                                        · rcases p5182_3 (m.d 2 3) (by simp) with h5195 | h5195
                                          · linarith only [h5162, h5195, hlam]
                                          · linarith only [h5177, h5195, hlam]
                                        · linarith only [h5171, h5194, hlam]
                                      · linarith only [h5193, hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p5182_1, u0ehi1]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5177, hc12, hlam, hphi, ht01, ht0b, ht5b, p5182_1, u5ehi3]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      rcases p5182_3 (m.d 0 2) (by simp) with h5203 | h5203
                                      · linarith only [h0, h5203, hlam]
                                      · linarith only [h5163, h5203, hlam]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      rcases p5182_3 (m.d 0 2) (by simp) with h5206 | h5206
                                      · linarith only [h0, h5206, hlam]
                                      · linarith only [h5164, h5206, hlam]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5162, hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5169, hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      rcases p5182_3 (m.d 0 2) (by simp) with h5212 | h5212
                                      · rcases p5182_3 (m.d 1 2) (by simp) with h5213 | h5213
                                        · rcases p5182_3 (m.d 2 3) (by simp) with h5214 | h5214
                                          · rcases p5182_3 (m.d 2 4) (by simp) with h5215 | h5215
                                            · linarith only [h5176, h5215, hlam]
                                            · rcases p5182_3 (m.d 2 5) (by simp) with h5217 | h5217
                                              · linarith only [h5177, h5217, hlam]
                                              · linarith only [h5178, h5217, hlam]
                                          · linarith only [h5176, h5214, hlam]
                                        · linarith only [h5170, h5213, hlam]
                                      · linarith only [h5163, h5212, hlam]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5162, h5177, hc02, hlam, hphi, ht0b, ht5b, p5182_1, u5ehi3]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5163, hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5170, hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5176, hlam, p5182_1]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5178, hlam, p5182_1]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5164, hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5171, hlam, p5182_0]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [h5177, hlam, p5182_1]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      rcases p5182_3 (m.d 0 2) (by simp) with h5232 | h5232
                                      · rcases p5182_3 (m.d 1 2) (by simp) with h5233 | h5233
                                        · rcases p5182_3 (m.d 2 3) (by simp) with h5234 | h5234
                                          · rcases p5182_3 (m.d 2 4) (by simp) with h5235 | h5235
                                            · linarith only [h5178, h5235, hlam]
                                            · rcases p5182_3 (m.d 2 5) (by simp) with h5237 | h5237
                                              · rcases h3bigk with h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h3977, hlam, p5238_1]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h0, h5162, h5177, hc12, hlam, hphi, ht01, ht0b, ht5b, p5238_1, u5ehi3]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  rcases p5238_3 (m.d 0 3) (by simp) with h5242 | h5242
                                                  · rcases p5238_3 (m.d 1 3) (by simp) with h5243 | h5243
                                                    · rcases p5238_3 (m.d 2 3) (by simp) with h5244 | h5244
                                                      · linarith only [h5162, h5244, hlam]
                                                      · linarith only [h5176, h5244, hlam]
                                                    · linarith only [h5172, h5243, hlam]
                                                  · linarith only [h5242, hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  rcases p5238_3 (m.d 0 3) (by simp) with h5249 | h5249
                                                  · rcases p5238_3 (m.d 1 3) (by simp) with h5250 | h5250
                                                    · rcases p5238_3 (m.d 2 3) (by simp) with h5251 | h5251
                                                      · linarith only [h5162, h5251, hlam]
                                                      · linarith only [h5177, h5251, hlam]
                                                    · linarith only [h5173, h5250, hlam]
                                                  · linarith only [h5249, hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h5169, hc12, hlam, hphi, ht01, p5238_1, u0ehi2]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h4846, h4847, h5169, h5174, h5176, h5177, hc12, hc34, hc45, hlam, hphi, ht01, p5182_1, p5238_1, u0ehi3]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  rcases p5238_3 (m.d 0 3) (by simp) with h5259 | h5259
                                                  · linarith only [h3977, h5259, hlam]
                                                  · linarith only [h5165, h5259, hlam]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  rcases p5238_3 (m.d 0 3) (by simp) with h5262 | h5262
                                                  · linarith only [h3977, h5262, hlam]
                                                  · linarith only [h5166, h5262, hlam]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h5162, hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h5169, hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  rcases p5238_3 (m.d 0 3) (by simp) with h5268 | h5268
                                                  · rcases p5238_3 (m.d 1 3) (by simp) with h5269 | h5269
                                                    · rcases p5238_3 (m.d 2 3) (by simp) with h5270 | h5270
                                                      · rcases p5238_3 (m.d 3 4) (by simp) with h5271 | h5271
                                                        · linarith only [h5271, hlam, p5238_0]
                                                        · rcases p5238_3 (m.d 3 5) (by simp) with h5273 | h5273
                                                          · linarith only [h5177, h5273, hlam]
                                                          · linarith only [h5180, h5273, hlam]
                                                      · linarith only [h5270, hlam, p5238_0]
                                                    · linarith only [h5172, h5269, hlam]
                                                  · linarith only [h5165, h5268, hlam]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h0, h5162, hc12, hlam, hphi, ht01, ht0b, ht5b, p5238_1, u5ehi3]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h5165, hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h5172, hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h5176, hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h5180, hlam, p5238_1]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h5166, hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h5173, hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h5177, hlam, p5238_0]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [h0, h4846, h4847, h5162, h5174, h5177, hc12, hc34, hc45, hlam, hphi, ht01, p5238_1, u0ehi3]
                                                · have p5238_0 := h5238c.1
                                                  have p5238_1 := h5238c.2.1
                                                  have p5238_2 := h5238c.2.2.1
                                                  have p5238_3 := h5238c.2.2.2
                                                  linarith only [hlam, p5238_0]
                                              · linarith only [h5178, h5237, hlam]
                                          · linarith only [h5176, h5234, hlam]
                                        · linarith only [h5170, h5233, hlam]
                                      · linarith only [h5163, h5232, hlam]
                                    · have p5182_0 := h5182c.1
                                      have p5182_1 := h5182c.2.1
                                      have p5182_2 := h5182c.2.2.1
                                      have p5182_3 := h5182c.2.2.2
                                      linarith only [hlam, p5182_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5295 | h5295
                                · linarith only [h4846, h4847, h5174, h5295, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5297 | h5297
                                  · linarith only [h4846, h4847, h5174, h5297, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                                  · rcases h2bigk with h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h0, hlam, p5299_1]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      rcases p5299_3 (m.d 0 2) (by simp) with h5302 | h5302
                                      · rcases p5299_3 (m.d 1 2) (by simp) with h5303 | h5303
                                        · rcases p5299_3 (m.d 2 3) (by simp) with h5304 | h5304
                                          · linarith only [h5304, hlam, p5299_0]
                                          · rcases p5299_3 (m.d 2 4) (by simp) with h5306 | h5306
                                            · linarith only [h5163, h5306, hlam]
                                            · rcases p5299_3 (m.d 2 5) (by simp) with h5308 | h5308
                                              · linarith only [h5164, h5308, hlam]
                                              · linarith only [h5177, h5308, hlam]
                                        · linarith only [h5169, h5303, hlam]
                                      · linarith only [h5302, hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      rcases p5299_3 (m.d 0 2) (by simp) with h5313 | h5313
                                      · rcases p5299_3 (m.d 1 2) (by simp) with h5314 | h5314
                                        · rcases p5299_3 (m.d 2 3) (by simp) with h5315 | h5315
                                          · linarith only [h5162, h5315, hlam]
                                          · linarith only [h5176, h5315, hlam]
                                        · linarith only [h5170, h5314, hlam]
                                      · linarith only [h5313, hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      rcases p5299_3 (m.d 0 2) (by simp) with h5320 | h5320
                                      · rcases p5299_3 (m.d 1 2) (by simp) with h5321 | h5321
                                        · rcases p5299_3 (m.d 2 3) (by simp) with h5322 | h5322
                                          · linarith only [h5162, h5322, hlam]
                                          · rcases p5299_3 (m.d 2 4) (by simp) with h5324 | h5324
                                            · linarith only [h5163, h5324, hlam]
                                            · rcases p5299_3 (m.d 2 5) (by simp) with h5326 | h5326
                                              · linarith only [h5326, hlam, p5299_0]
                                              · rcases h3bigk with h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c | h5328c
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h3977, hlam, p5328_1]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  rcases p5328_3 (m.d 0 3) (by simp) with h5331 | h5331
                                                  · rcases p5328_3 (m.d 1 3) (by simp) with h5332 | h5332
                                                    · rcases p5328_3 (m.d 2 3) (by simp) with h5333 | h5333
                                                      · linarith only [h5162, h5333, hlam]
                                                      · rcases p5328_3 (m.d 3 4) (by simp) with h5335 | h5335
                                                        · linarith only [h5165, h5335, hlam]
                                                        · rcases p5328_3 (m.d 3 5) (by simp) with h5337 | h5337
                                                          · linarith only [h5166, h5337, hlam]
                                                          · linarith only [h5177, h5337, hlam]
                                                    · linarith only [h5169, h5332, hlam]
                                                  · linarith only [h5162, h5331, hlam]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h5166, h5176, h5177, hlam, p5328_2]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h3977, h4846, h4847, h5174, h5176, h5177, hc13, hc34, hc45, hlam, hphi, ht01, p5328_1, u0ehi3]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [hc13, hlam, hphi, ht01, p5328_1, u0ehi2]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  rcases p5328_3 (m.d 0 3) (by simp) with h5346 | h5346
                                                  · linarith only [h3977, h5346, hlam]
                                                  · linarith only [h5162, h5346, hlam]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h3977, h5166, h5176, h5177, hlam, p5328_2]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h4846, h4847, h5174, h5176, h5177, hc13, hc34, hc45, hlam, hphi, ht01, p5328_1, u0ehi3]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h5162, hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h5169, hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h4846, h4847, h5166, h5174, h5177, hc03, hc34, hc45, hlam, hphi, p5328_1, u0ehi3]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h5177, hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h5165, hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h5172, hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h5176, hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h5297, hlam, p5328_1]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h5166, hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h5173, hlam, p5328_0]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [h0, h4846, h4847, h5162, h5166, h5174, h5176, hc12, hc34, hc45, hlam, hphi, ht01, p5328_1, u0ehi3]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  rcases p5328_3 (m.d 0 3) (by simp) with h5364 | h5364
                                                  · rcases p5328_3 (m.d 1 3) (by simp) with h5365 | h5365
                                                    · rcases p5328_3 (m.d 2 3) (by simp) with h5366 | h5366
                                                      · linarith only [h5177, h5366, hlam]
                                                      · linarith only [h5176, h5366, hlam]
                                                    · linarith only [h5172, h5365, hlam]
                                                  · linarith only [h5165, h5364, hlam]
                                                · have p5328_0 := h5328c.1
                                                  have p5328_1 := h5328c.2.1
                                                  have p5328_2 := h5328c.2.2.1
                                                  have p5328_3 := h5328c.2.2.2
                                                  linarith only [hlam, p5328_0]
                                        · linarith only [h5171, h5321, hlam]
                                      · linarith only [h5320, hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h5162, h5166, hc12, hlam, hphi, ht01, ht0b, ht5b, p5299_1, u5ehi3]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      rcases p5299_3 (m.d 0 2) (by simp) with h5376 | h5376
                                      · linarith only [h0, h5376, hlam]
                                      · linarith only [h5162, h5376, hlam]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      rcases p5299_3 (m.d 0 2) (by simp) with h5379 | h5379
                                      · linarith only [h0, h5379, hlam]
                                      · linarith only [h5163, h5379, hlam]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      rcases p5299_3 (m.d 0 2) (by simp) with h5382 | h5382
                                      · linarith only [h0, h5382, hlam]
                                      · linarith only [h5164, h5382, hlam]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h5162, hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h5169, hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h4846, h4847, h5162, h5166, h5174, h5177, hc02, hc24, hc45, hlam, hphi, p5299_1, u0ehi3]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h5177, hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h5163, hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h5170, hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h5176, hlam, p5299_1]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h5295, hlam, p5299_1]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h5164, hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h5171, hlam, p5299_0]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [h0, h4846, h4847, h5164, h5174, h5176, hc12, hc34, hc45, hlam, hphi, ht01, p5299_1, u0ehi3]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      rcases p5299_3 (m.d 0 2) (by simp) with h5398 | h5398
                                      · rcases p5299_3 (m.d 1 2) (by simp) with h5399 | h5399
                                        · rcases p5299_3 (m.d 2 3) (by simp) with h5400 | h5400
                                          · linarith only [h5177, h5400, hlam]
                                          · linarith only [h5176, h5400, hlam]
                                        · linarith only [h5170, h5399, hlam]
                                      · linarith only [h5163, h5398, hlam]
                                    · have p5299_0 := h5299c.1
                                      have p5299_1 := h5299c.2.1
                                      have p5299_2 := h5299c.2.2.1
                                      have p5299_3 := h5299c.2.2.2
                                      linarith only [hlam, p5299_0]
                            · linarith only [h4846, h4847, h5172, h5174, h5176, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h3977, h4846, h5162, h5166, h5173, hc12, hlam, hphi, ht01, u0ehi3]
                      · linarith only [h3977, h4846, h5172, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · linarith only [h0, h4846, h5164, h5166, h5171, hc03, hlam, hphi, u0ehi3]
                  · linarith only [h0, h4846, h5170, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                · linarith only [h0, h4846, h5169, hc23, hlam, hphi, ht01, ht12, u0ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5412 | h5412
              · linarith only [h4846, h4847, h5412, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5414 | h5414
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5415 | h5415
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5416 | h5416
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5417 | h5417
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5418 | h5418
                        · linarith only [h5166, h5418, hc13, hlam, hphi, ht01, u0ehi2]
                        · linarith only [h3977, h5418, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h3977, h4846, h5417, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · linarith only [h0, h4846, h5416, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h3977, h4846, h5414, h5415, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                · linarith only [h0, h4846, h5162, h5414, hc02, hlam, hphi, u0ehi3]
          · linarith only [h3977, h4846, h5165, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5426 | h5426
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5427 | h5427
            · linarith only [h5162, h5164, h5427, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5429 | h5429
              · linarith only [h3977, h4846, h5162, h5164, h5429, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5431 | h5431
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5432 | h5432
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5433 | h5433
                    · linarith only [h3977, h5162, h5164, h5433, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h4846, h5433, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h3977, h4846, h5431, h5432, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                · linarith only [h0, h4846, h5162, h5164, h5431, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h3977, h4846, h5426, hlam]
      · linarith only [h0, h4846, h5163, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5440 | h5440
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5441 | h5441
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5442 | h5442
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5443 | h5443
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5444 | h5444
              · linarith only [h4846, h4847, h5444, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5446 | h5446
                · linarith only [h5162, h5441, h5446, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h4846, h5446, hc23, hlam, hphi, ht01, ht12, u0ehi3]
            · linarith only [h5162, h5441, h5443, hlam]
          · linarith only [h4846, h4847, h5162, h5441, h5442, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5451 | h5451
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5452 | h5452
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5453 | h5453
              · linarith only [h0, h4846, h5441, h5453, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5455 | h5455
                · linarith only [h0, h5162, h5455, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h4846, h5455, hc23, hlam, hphi, ht01, ht12, u0ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5458 | h5458
              · linarith only [h0, h4846, h5162, h5452, h5458, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5460 | h5460
                · linarith only [h0, h5162, h5460, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h4846, h5460, hc23, hlam, hphi, ht01, ht12, u0ehi3]
          · linarith only [h0, h4846, h5162, h5451, hlam]
      · linarith only [h0, h4846, h5440, hlam]

end R2N4
