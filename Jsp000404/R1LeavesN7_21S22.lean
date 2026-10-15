import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S21

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4238 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4336 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  have h4238 := hg4238
  rcases m.htr 0 2 5 (by decide) (by decide) with h5860 | h5860
  · rcases m.htr 0 3 5 (by decide) (by decide) with h5861 | h5861
    · rcases m.htr 0 4 5 (by decide) (by decide) with h5862 | h5862
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5863 | h5863
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5864 | h5864
          · linarith only [h4336, h5860, h5864, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5866 | h5866
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5867 | h5867
              · linarith only [h5863, h5864, h5867, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5869 | h5869
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5870 | h5870
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5871 | h5871
                    · linarith only [h4335, h5867, h5869, h5871, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5873 | h5873
                      · linarith only [h0, h4335, h5864, h5871, h5873, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · linarith only [h0, h4335, h5861, h5864, h5871, h5873, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h4335, h5861, h5862, h5864, h5870, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h3473, h5861, h5869, hlam]
            · linarith only [h0, h5860, h5866, hlam]
        · linarith only [h0, h4335, h5863, hlam]
      · linarith only [h4335, h4336, h5861, h5862, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h5881 | h5881
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5882 | h5882
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5883 | h5883
          · linarith only [h4336, h5860, h5883, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5885 | h5885
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5886 | h5886
              · linarith only [h5882, h5883, h5886, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5888 | h5888
                · linarith only [h5861, h5886, h5888, hc03, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5890 | h5890
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5891 | h5891
                    · linarith only [h0, h4335, h5883, h5891, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5893 | h5893
                      · linarith only [h0, h4335, h5883, h5888, h5891, h5893, hc13, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5895 | h5895
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5896 | h5896
                          · rcases h1bigk with h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h0, hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h3473, hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h4044, hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h4238, hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h5883, h5891, hc01, hc34, hlam, hphi, ht12, ht23, p5897_1]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h3473, h5883, h5891, hc01, hc34, hlam, hphi, ht12, ht23, p5897_1]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h5883, hlam, p5897_1]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h5883, h5891, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5897_1, u5ehi1]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h5888, hc01, hc35, hlam, hphi, ht12, ht23, p5897_1]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h5882, hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h5886, hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h5888, hlam, p5897_1]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              rcases p5897_3 (m.d 0 1) (by simp) with h5913 | h5913
                              · linarith only [h5913, hlam, p5897_0]
                              · rcases p5897_3 (m.d 1 2) (by simp) with h5915 | h5915
                                · linarith only [h5883, h5915, hlam]
                                · linarith only [h0, h5915, hlam]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h0, h5860, hc14, hlam, hphi, ht01, ht0b, ht5b, p5897_1, u5ehi2]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h3473, h5883, h5891, hc01, hc34, hlam, hphi, ht12, ht23, p5897_1]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h4238, h5883, h5891, hc01, hc34, hlam, hphi, ht12, ht23, p5897_1]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h5883, h5885, h5891, hc01, hc34, hlam, hphi, ht12, ht23, p5897_1]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h5885, hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h3473, h5883, h5885, h5891, hc01, hc34, hlam, hphi, ht12, ht23, p5897_1]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [h5890, hlam, p5897_0]
                            · have p5897_0 := h5897c.1
                              have p5897_1 := h5897c.2.1
                              have p5897_2 := h5897c.2.2.1
                              have p5897_3 := h5897c.2.2.2
                              linarith only [hlam, p5897_0]
                          · linarith only [h0, h5860, h5883, h5891, h5895, h5896, hlam]
                        · linarith only [h0, h5860, h5883, h5893, h5895, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h4044, h5881, h5890, hlam]
            · linarith only [h0, h5860, h5885, hlam]
        · linarith only [h0, h4335, h5882, hlam]
      · linarith only [h4336, h5860, h5881, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h5933 | h5933
    · linarith only [h4335, h5860, h5933, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h5935 | h5935
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5936 | h5936
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5937 | h5937
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5938 | h5938
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5939 | h5939
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5940 | h5940
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5941 | h5941
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5942 | h5942
                    · linarith only [h4335, h4336, h5937, h5942, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5944 | h5944
                      · linarith only [h4335, h4336, h5933, h5936, h5939, h5942, h5944, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5946 | h5946
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5947 | h5947
                          · rcases h1bigk with h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c | h5948c
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h0, hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h3473, hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h4044, hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h4238, hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              rcases p5948_3 (m.d 0 1) (by simp) with h5954 | h5954
                              · linarith only [h5954, hlam, p5948_0]
                              · rcases p5948_3 (m.d 1 2) (by simp) with h5956 | h5956
                                · rcases p5948_3 (m.d 1 3) (by simp) with h5957 | h5957
                                  · linarith only [h5936, h5957, hlam]
                                  · linarith only [h3473, h5957, hlam]
                                · linarith only [h5956, hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h5860, h5939, h5942, h5946, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5948_1]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h4335, h5860, h5940, h5941, h5944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5948_1]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h4335, h5860, h5940, h5944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5948_1]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              rcases p5948_3 (m.d 0 1) (by simp) with h5965 | h5965
                              · linarith only [h5965, hlam, p5948_0]
                              · rcases p5948_3 (m.d 1 2) (by simp) with h5967 | h5967
                                · rcases p5948_3 (m.d 1 3) (by simp) with h5968 | h5968
                                  · rcases p5948_3 (m.d 1 4) (by simp) with h5969 | h5969
                                    · linarith only [h5939, h5969, hlam]
                                    · linarith only [h4044, h5969, hlam]
                                  · linarith only [h5968, hlam, p5948_0]
                                · linarith only [h0, h5967, hlam]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h5936, hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h4335, h5860, h5940, h5941, h5944, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5948_1]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h4335, h5860, h5936, h5940, h5944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5948_1]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              rcases p5948_3 (m.d 0 1) (by simp) with h5978 | h5978
                              · linarith only [h5978, hlam, p5948_0]
                              · rcases p5948_3 (m.d 1 2) (by simp) with h5980 | h5980
                                · rcases p5948_3 (m.d 1 3) (by simp) with h5981 | h5981
                                  · rcases p5948_3 (m.d 1 4) (by simp) with h5982 | h5982
                                    · rcases p5948_3 (m.d 1 5) (by simp) with h5983 | h5983
                                      · linarith only [h5941, h5983, hlam]
                                      · linarith only [h4238, h5983, hlam]
                                    · linarith only [h5982, hlam, p5948_0]
                                  · linarith only [h3473, h5981, hlam]
                                · linarith only [h0, h5980, hlam]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h5937, hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h5939, hlam, p5948_1]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h4335, h5860, h5940, h5944, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5948_1]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              rcases p5948_3 (m.d 0 1) (by simp) with h5993 | h5993
                              · linarith only [h5993, hlam, p5948_0]
                              · rcases p5948_3 (m.d 1 2) (by simp) with h5995 | h5995
                                · rcases p5948_3 (m.d 1 3) (by simp) with h5996 | h5996
                                  · rcases p5948_3 (m.d 1 4) (by simp) with h5997 | h5997
                                    · rcases p5948_3 (m.d 1 5) (by simp) with h5998 | h5998
                                      · rcases h2bigk with h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c | h5999c
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h0, hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h5860, h5942, h5946, hc23, hc34, hlam, hphi, p5999_1]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h4336, hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h5860, hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          rcases p5999_3 (m.d 0 2) (by simp) with h6005 | h6005
                                          · linarith only [h0, h6005, hlam]
                                          · rcases p5999_3 (m.d 1 2) (by simp) with h6007 | h6007
                                            · rcases p5999_3 (m.d 2 3) (by simp) with h6008 | h6008
                                              · linarith only [h5936, h6008, hlam]
                                              · rcases p5999_3 (m.d 2 4) (by simp) with h6010 | h6010
                                                · linarith only [h5937, h6010, hlam]
                                                · linarith only [h4336, h6010, hlam]
                                            · linarith only [h0, h6007, hlam]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h4335, h5860, h5936, h5939, h5942, h5946, hlam, p5999_2]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h4335, h5860, h5946, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5999_1]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h4335, h5860, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5999_1]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h4335, hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h5936, hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h5942, hlam, p5999_1]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h5944, hlam, p5999_1]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h4335, h5937, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5999_1]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h5937, hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          rcases p5999_3 (m.d 0 2) (by simp) with h6025 | h6025
                                          · linarith only [h4336, h6025, hlam]
                                          · linarith only [h4335, h6025, hlam]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h4335, h5860, h5936, h5939, h5942, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5999_1]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h4335, h5938, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5999_1]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h5938, hlam, p5999_0]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          rcases p5999_3 (m.d 0 2) (by simp) with h6032 | h6032
                                          · linarith only [h5860, h6032, hlam]
                                          · linarith only [h4335, h6032, hlam]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [h5946, hlam, p5999_1]
                                        · have p5999_0 := h5999c.1
                                          have p5999_1 := h5999c.2.1
                                          have p5999_2 := h5999c.2.2.1
                                          have p5999_3 := h5999c.2.2.2
                                          linarith only [hlam, p5999_0]
                                      · linarith only [h5998, hlam, p5948_0]
                                    · linarith only [h4044, h5997, hlam]
                                  · linarith only [h3473, h5996, hlam]
                                · linarith only [h0, h5995, hlam]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h5938, hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h5940, hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [h5941, hlam, p5948_0]
                            · have p5948_0 := h5948c.1
                              have p5948_1 := h5948c.2.1
                              have p5948_2 := h5948c.2.2.1
                              have p5948_3 := h5948c.2.2.2
                              linarith only [hlam, p5948_0]
                          · linarith only [h4335, h4336, h5935, h5942, h5947, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · linarith only [h4336, h5935, h5946, hlam]
                  · linarith only [h4044, h4336, h5935, h5941, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h4335, h4336, h5937, h5939, h5940, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6049 | h6049
                · linarith only [h3473, h5933, h5939, h6049, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6051 | h6051
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6052 | h6052
                    · linarith only [h4335, h5860, h5938, h5939, h6051, h6052, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6054 | h6054
                      · linarith only [h3473, h4335, h6049, h6054, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6056 | h6056
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6057 | h6057
                          · rcases h1bigk with h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h0, hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h3473, hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h4044, hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h4238, hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              rcases p6058_3 (m.d 0 1) (by simp) with h6064 | h6064
                              · linarith only [h6064, hlam, p6058_0]
                              · rcases p6058_3 (m.d 1 2) (by simp) with h6066 | h6066
                                · rcases p6058_3 (m.d 1 3) (by simp) with h6067 | h6067
                                  · linarith only [h5936, h6067, hlam]
                                  · linarith only [h3473, h6067, hlam]
                                · linarith only [h6066, hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h3473, hc01, hc12, hlam, hphi, p6058_1]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h4044, hc01, hc12, hlam, hphi, p6058_1]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h4335, h5860, h5938, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6058_1]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h6049, hc01, hc35, hlam, hphi, ht12, ht23, p6058_1]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h5936, hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h5939, hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h6049, hlam, p6058_1]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              rcases p6058_3 (m.d 0 1) (by simp) with h6080 | h6080
                              · linarith only [h6080, hlam, p6058_0]
                              · rcases p6058_3 (m.d 1 2) (by simp) with h6082 | h6082
                                · rcases p6058_3 (m.d 1 3) (by simp) with h6083 | h6083
                                  · linarith only [h5939, h6083, hlam]
                                  · linarith only [h3473, h6083, hlam]
                                · linarith only [h0, h6082, hlam]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h5937, hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h3473, hc01, hc14, hlam, hphi, p6058_1]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h4335, h5860, h5938, h5939, hc23, hc34, hlam, hphi, p6058_1]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              rcases p6058_3 (m.d 0 1) (by simp) with h6091 | h6091
                              · linarith only [h6091, hlam, p6058_0]
                              · rcases p6058_3 (m.d 1 2) (by simp) with h6093 | h6093
                                · rcases p6058_3 (m.d 1 3) (by simp) with h6094 | h6094
                                  · linarith only [h6049, h6094, hlam]
                                  · linarith only [h3473, h6094, hlam]
                                · linarith only [h0, h6093, hlam]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h5938, hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h3473, hc01, hc15, hlam, hphi, p6058_1]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [h6051, hlam, p6058_0]
                            · have p6058_0 := h6058c.1
                              have p6058_1 := h6058c.2.1
                              have p6058_2 := h6058c.2.2.1
                              have p6058_3 := h6058c.2.2.2
                              linarith only [hlam, p6058_0]
                          · linarith only [h4044, h5935, h5939, h6057, hlam]
                        · linarith only [h4335, h4336, h5935, h6056, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h4336, h5935, h5937, h6051, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
            · linarith only [h4336, h5935, h5937, h5938, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6106 | h6106
            · linarith only [h4335, h5860, h5937, h6106, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6108 | h6108
              · linarith only [h5936, h5937, h6108, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6110 | h6110
                · linarith only [h5933, h6108, h6110, hc03, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6112 | h6112
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6113 | h6113
                    · linarith only [h0, h4335, h5937, h6108, h6113, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6115 | h6115
                      · linarith only [h3473, h6110, h6115, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6117 | h6117
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6118 | h6118
                          · rcases h1bigk with h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c | h6119c
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h0, hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h3473, hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h4044, hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h4238, hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h6106, h6113, h6117, hc01, hc34, hlam, hphi, ht12, ht23, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h6106, h6113, h6117, hc13, hc34, hlam, hphi, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h5937, hlam, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h6106, hlam, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h5936, h6106, h6113, h6117, hc01, hc34, hlam, hphi, ht12, ht23, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h5936, hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h6108, hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h6110, hlam, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              rcases p6119_3 (m.d 0 1) (by simp) with h6135 | h6135
                              · linarith only [h6135, hlam, p6119_0]
                              · rcases p6119_3 (m.d 1 2) (by simp) with h6137 | h6137
                                · linarith only [h5937, h6137, hlam]
                                · linarith only [h0, h6137, hlam]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h3473, hc01, hc14, hlam, hphi, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h3473, h5936, h5937, h6106, h6113, hc01, hc34, hlam, hphi, ht12, ht23, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              rcases p6119_3 (m.d 0 1) (by simp) with h6144 | h6144
                              · linarith only [h6144, hlam, p6119_0]
                              · rcases p6119_3 (m.d 1 2) (by simp) with h6146 | h6146
                                · linarith only [h6106, h6146, hlam]
                                · linarith only [h0, h6146, hlam]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h3473, h5936, hc01, hc15, hlam, hphi, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h3473, hc01, hc15, hlam, hphi, p6119_1]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [h6112, hlam, p6119_0]
                            · have p6119_0 := h6119c.1
                              have p6119_1 := h6119c.2.1
                              have p6119_2 := h6119c.2.2.1
                              have p6119_3 := h6119c.2.2.2
                              linarith only [hlam, p6119_0]
                          · linarith only [h4044, h5935, h5937, h6113, h6118, hlam]
                        · linarith only [h3473, h5935, h5936, h5937, h6117, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h4044, h5935, h6112, hlam]
        · linarith only [h0, h4335, h5936, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6157 | h6157
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6158 | h6158
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6159 | h6159
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6160 | h6160
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6161 | h6161
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6162 | h6162
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6163 | h6163
                    · linarith only [h4335, h4336, h5935, h6157, h6160, h6162, h6163, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6165 | h6165
                      · linarith only [h4335, h4336, h5933, h5935, h6157, h6160, h6162, h6165, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6167 | h6167
                        · linarith only [h4335, h4336, h5935, h6163, h6167, hc23, hc34, hlam, hphi]
                        · linarith only [h4335, h4336, h6157, h6160, h6162, h6167, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h4335, h4336, h6158, h6162, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h4335, h4336, h6158, h6160, h6161, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6172 | h6172
                · linarith only [h5933, h6160, h6172, hc03, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6174 | h6174
                  · linarith only [h4335, h4336, h5935, h6160, h6174, hc23, hc34, hlam, hphi]
                  · linarith only [h4335, h4336, h6158, h6174, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4335, h4336, h6158, h6159, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6178 | h6178
            · linarith only [h4335, h5860, h6158, h6178, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6180 | h6180
              · linarith only [h6157, h6158, h6180, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6182 | h6182
                · linarith only [h3473, h5933, h6180, h6182, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6184 | h6184
                  · linarith only [h4335, h4336, h5935, h6180, h6184, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6186 | h6186
                    · linarith only [h0, h4335, h6158, h6184, h6186, hc45, hlam, hphi, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6188 | h6188
                      · linarith only [h0, h4335, h6158, h6184, h6188, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6190 | h6190
                        · linarith only [h0, h4335, h6158, h6184, h6186, h6190, hc23, hc34, hlam, hphi]
                        · linarith only [h4335, h4336, h6190, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h4335, h4336, h6157, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4238 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  have h4238 := hg4238
  rcases m.htr 0 2 4 (by decide) (by decide) with h4336 | h4336
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg3473 hg4044 hg4238 h4335 h4336
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg3473 hg4044 hg4238 h4335 h4336

end R2N4
