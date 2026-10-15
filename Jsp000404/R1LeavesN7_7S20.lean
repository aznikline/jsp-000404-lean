import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 0 3 5 (by decide) (by decide) with h12237 | h12237
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 0 3 5 (by decide) (by decide) with h13923 | h13923
  · rcases m.htr 0 4 5 (by decide) (by decide) with h13924 | h13924
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13925 | h13925
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13926 | h13926
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13927 | h13927
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13928 | h13928
            · linarith only [h12236, h13923, h13928, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13930 | h13930
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13931 | h13931
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13932 | h13932
                  · linarith only [h12233, h13928, h13930, h13932, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13934 | h13934
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13935 | h13935
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13936 | h13936
                        · rcases h1bigk with h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c | h13937c
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h0, hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h10472, hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h11379, hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h12013, hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            rcases p13937_3 (m.d 0 1) (by simp) with h13943 | h13943
                            · linarith only [h13943, hlam, p13937_0]
                            · rcases p13937_3 (m.d 1 2) (by simp) with h13945 | h13945
                              · rcases p13937_3 (m.d 1 3) (by simp) with h13946 | h13946
                                · linarith only [h13925, h13946, hlam]
                                · linarith only [h10472, h13946, hlam]
                              · linarith only [h13945, hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h10472, h12233, h13934, h13936, hc12, hlam, hphi, ht01, ht0b, ht5b, p13937_1, u5ehi4]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h11379, hc01, hc12, hlam, hphi, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h12013, hc01, hc12, hlam, hphi, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h13928, hc01, hc34, hlam, hphi, ht12, ht23, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h13925, hlam, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h13928, hlam, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h12013, h13928, hc01, hc34, hlam, hphi, ht12, ht23, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            rcases p13937_3 (m.d 0 1) (by simp) with h13959 | h13959
                            · linarith only [h13959, hlam, p13937_0]
                            · rcases p13937_3 (m.d 1 2) (by simp) with h13961 | h13961
                              · rcases p13937_3 (m.d 1 3) (by simp) with h13962 | h13962
                                · linarith only [h13928, h13962, hlam]
                                · linarith only [h10472, h13962, hlam]
                              · linarith only [h0, h13961, hlam]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h13926, hlam, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h10472, hc01, hc14, hlam, hphi, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h12013, h13928, hc01, hc34, hlam, hphi, ht12, ht23, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h13928, h13930, hc01, hc34, hlam, hphi, ht12, ht23, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h13927, hlam, p13937_1]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h13930, hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [h13931, hlam, p13937_0]
                          · have p13937_0 := h13937c.1
                            have p13937_1 := h13937c.2.1
                            have p13937_2 := h13937c.2.2.1
                            have p13937_3 := h13937c.2.2.2
                            linarith only [hlam, p13937_0]
                        · linarith only [h10472, h13928, h13936, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h10472, h13923, h13924, h13928, h13932, h13934, h13935, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · linarith only [h10472, h13923, h13928, h13934, hc23, hc34, hlam, hphi]
                · linarith only [h10472, h11379, h13923, h13924, h13928, h13931, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h10472, h13923, h13930, hlam]
          · linarith only [h0, h12233, h12235, h13923, h13927, hlam]
        · linarith only [h0, h12234, h13926, hlam]
      · linarith only [h0, h12233, h13925, hlam]
    · linarith only [h12236, h13923, h13924, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h13984 | h13984
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13985 | h13985
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13986 | h13986
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13987 | h13987
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13988 | h13988
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13989 | h13989
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13990 | h13990
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13991 | h13991
                  · linarith only [h0, h12233, h12236, h13984, h13991, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13993 | h13993
                    · linarith only [h12233, h13923, h13993, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13995 | h13995
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13996 | h13996
                        · rcases h1bigk with h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c | h13997c
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h0, hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h10472, hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h11379, hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h12013, hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            rcases p13997_3 (m.d 0 1) (by simp) with h14003 | h14003
                            · linarith only [h14003, hlam, p13997_0]
                            · rcases p13997_3 (m.d 1 2) (by simp) with h14005 | h14005
                              · rcases p13997_3 (m.d 1 3) (by simp) with h14006 | h14006
                                · linarith only [h13985, h14006, hlam]
                                · linarith only [h10472, h14006, hlam]
                              · linarith only [h14005, hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h13923, h13988, h13996, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13997_1]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h11379, hc01, hc12, hlam, hphi, p13997_1]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h12013, hc01, hc12, hlam, hphi, p13997_1]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            rcases p13997_3 (m.d 0 1) (by simp) with h14014 | h14014
                            · linarith only [h14014, hlam, p13997_0]
                            · rcases p13997_3 (m.d 1 2) (by simp) with h14016 | h14016
                              · rcases p13997_3 (m.d 1 3) (by simp) with h14017 | h14017
                                · rcases p13997_3 (m.d 1 4) (by simp) with h14018 | h14018
                                  · linarith only [h13988, h14018, hlam]
                                  · linarith only [h11379, h14018, hlam]
                                · linarith only [h14017, hlam, p13997_0]
                              · linarith only [h0, h14016, hlam]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h13985, hlam, p13997_1]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h12234, h12236, h13988, h13995, hc13, hlam, hphi, ht01, ht0b, ht5b, p13997_1, u5ehi4]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h10472, h13923, h13985, h13989, hc01, hc12, hlam, hphi, p13997_1]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            rcases p13997_3 (m.d 0 1) (by simp) with h14027 | h14027
                            · linarith only [h14027, hlam, p13997_0]
                            · rcases p13997_3 (m.d 1 2) (by simp) with h14029 | h14029
                              · rcases p13997_3 (m.d 1 3) (by simp) with h14030 | h14030
                                · rcases p13997_3 (m.d 1 4) (by simp) with h14031 | h14031
                                  · rcases p13997_3 (m.d 1 5) (by simp) with h14032 | h14032
                                    · linarith only [h13990, h14032, hlam]
                                    · linarith only [h12013, h14032, hlam]
                                  · linarith only [h14031, hlam, p13997_0]
                                · linarith only [h10472, h14030, hlam]
                              · linarith only [h0, h14029, hlam]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h13986, hlam, p13997_1]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h13988, hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h10472, h13923, h13989, hc01, hc14, hlam, hphi, p13997_1]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            rcases p13997_3 (m.d 0 1) (by simp) with h14042 | h14042
                            · linarith only [h14042, hlam, p13997_0]
                            · rcases p13997_3 (m.d 1 2) (by simp) with h14044 | h14044
                              · rcases p13997_3 (m.d 1 3) (by simp) with h14045 | h14045
                                · rcases p13997_3 (m.d 1 4) (by simp) with h14046 | h14046
                                  · rcases p13997_3 (m.d 1 5) (by simp) with h14047 | h14047
                                    · rcases h1emax with h14048 | h14048 | h14048 | h14048 | h14048
                                      · rcases h3bigk with h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c | h14049c
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h10472, hlam, p14049_1]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h13923, hc23, hc35, hlam, hphi, p14049_1]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h12236, hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h13923, hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          rcases p14049_3 (m.d 0 3) (by simp) with h14055 | h14055
                                          · linarith only [h10472, h14055, hlam]
                                          · rcases p14049_3 (m.d 1 3) (by simp) with h14057 | h14057
                                            · rcases p14049_3 (m.d 2 3) (by simp) with h14058 | h14058
                                              · linarith only [h13985, h14058, hlam]
                                              · rcases p14049_3 (m.d 3 4) (by simp) with h14060 | h14060
                                                · linarith only [h13988, h14060, hlam]
                                                · linarith only [h12236, h14060, hlam]
                                            · linarith only [h10472, h14057, hlam]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          rcases p14049_3 (m.d 0 3) (by simp) with h14065 | h14065
                                          · linarith only [h10472, h14065, hlam]
                                          · linarith only [h12233, h14065, hlam]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h12234, h12236, h13985, h13995, hc12, hlam, hphi, ht01, ht0b, ht5b, p14049_1, u5ehi4]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h10472, h13923, h13985, hc01, hc12, hlam, hphi, p14049_1]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h12233, hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h13985, hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h13991, hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h13993, hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h10472, h13985, h13988, hc01, hc12, hlam, hphi, p14049_1]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h13988, hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          rcases p14049_3 (m.d 0 3) (by simp) with h14077 | h14077
                                          · linarith only [h12236, h14077, hlam]
                                          · linarith only [h12233, h14077, hlam]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h13923, h13985, h13988, hc12, hlam, hphi, ht01, ht0b, ht5b, p14049_1, u5ehi0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h10472, h13985, h13989, hc01, hc12, hlam, hphi, p14049_1]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h13989, hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          rcases p14049_3 (m.d 0 3) (by simp) with h14084 | h14084
                                          · linarith only [h13923, h14084, hlam]
                                          · linarith only [h12233, h14084, hlam]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [h13996, hlam, p14049_0]
                                        · have p14049_0 := h14049c.1
                                          have p14049_1 := h14049c.2.1
                                          have p14049_2 := h14049c.2.2.1
                                          have p14049_3 := h14049c.2.2.2
                                          linarith only [hlam, p14049_0]
                                      · linarith only [h13985, h13988, h13996, h14048, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                      · linarith only [h12234, h12236, h13988, h13995, h14048, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                      · linarith only [h13990, h14048, hc01, hlam, p13997_1]
                                      · linarith only [h14048, hc01, hlam, p13997_1]
                                    · linarith only [h14047, hlam, p13997_0]
                                  · linarith only [h11379, h14046, hlam]
                                · linarith only [h10472, h14045, hlam]
                              · linarith only [h0, h14044, hlam]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h13987, hlam, p13997_1]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h13989, hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [h13990, hlam, p13997_0]
                          · have p13997_0 := h13997c.1
                            have p13997_1 := h13997c.2.1
                            have p13997_2 := h13997c.2.2.1
                            have p13997_3 := h13997c.2.2.2
                            linarith only [hlam, p13997_0]
                        · linarith only [h12234, h12236, h13995, h13996, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14102 | h14102
                        · rcases h1bigk with h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h0, hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h10472, hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h11379, hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h12013, hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            rcases p14103_3 (m.d 0 1) (by simp) with h14109 | h14109
                            · linarith only [h14109, hlam, p14103_0]
                            · rcases p14103_3 (m.d 1 2) (by simp) with h14111 | h14111
                              · rcases p14103_3 (m.d 1 3) (by simp) with h14112 | h14112
                                · linarith only [h13985, h14112, hlam]
                                · linarith only [h10472, h14112, hlam]
                              · linarith only [h14111, hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h10472, hc01, hc12, hlam, hphi, p14103_1]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h11379, hc01, hc12, hlam, hphi, p14103_1]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h12013, hc01, hc12, hlam, hphi, p14103_1]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            rcases p14103_3 (m.d 0 1) (by simp) with h14120 | h14120
                            · linarith only [h14120, hlam, p14103_0]
                            · rcases p14103_3 (m.d 1 2) (by simp) with h14122 | h14122
                              · rcases p14103_3 (m.d 1 3) (by simp) with h14123 | h14123
                                · rcases p14103_3 (m.d 1 4) (by simp) with h14124 | h14124
                                  · linarith only [h13988, h14124, hlam]
                                  · linarith only [h11379, h14124, hlam]
                                · linarith only [h14123, hlam, p14103_0]
                              · linarith only [h0, h14122, hlam]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h13985, hlam, p14103_1]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h12236, h13984, h13988, h13991, h13995, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14103_1]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h10472, h13923, h13985, h13989, hc01, hc12, hlam, hphi, p14103_1]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            rcases p14103_3 (m.d 0 1) (by simp) with h14133 | h14133
                            · linarith only [h14133, hlam, p14103_0]
                            · rcases p14103_3 (m.d 1 2) (by simp) with h14135 | h14135
                              · rcases p14103_3 (m.d 1 3) (by simp) with h14136 | h14136
                                · rcases p14103_3 (m.d 1 4) (by simp) with h14137 | h14137
                                  · rcases p14103_3 (m.d 1 5) (by simp) with h14138 | h14138
                                    · linarith only [h13990, h14138, hlam]
                                    · linarith only [h12013, h14138, hlam]
                                  · linarith only [h14137, hlam, p14103_0]
                                · linarith only [h10472, h14136, hlam]
                              · linarith only [h0, h14135, hlam]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h13986, hlam, p14103_1]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h13988, hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h10472, h13923, h13989, hc01, hc14, hlam, hphi, p14103_1]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            rcases p14103_3 (m.d 0 1) (by simp) with h14148 | h14148
                            · linarith only [h14148, hlam, p14103_0]
                            · rcases p14103_3 (m.d 1 2) (by simp) with h14150 | h14150
                              · rcases p14103_3 (m.d 1 3) (by simp) with h14151 | h14151
                                · rcases p14103_3 (m.d 1 4) (by simp) with h14152 | h14152
                                  · rcases p14103_3 (m.d 1 5) (by simp) with h14153 | h14153
                                    · rcases h1emax with h14154 | h14154 | h14154 | h14154 | h14154
                                      · rcases h3bigk with h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c | h14155c
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h10472, hlam, p14155_1]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h13923, hc23, hc35, hlam, hphi, p14155_1]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h12236, hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h13923, hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          rcases p14155_3 (m.d 0 3) (by simp) with h14161 | h14161
                                          · linarith only [h10472, h14161, hlam]
                                          · rcases p14155_3 (m.d 1 3) (by simp) with h14163 | h14163
                                            · rcases p14155_3 (m.d 2 3) (by simp) with h14164 | h14164
                                              · linarith only [h13985, h14164, hlam]
                                              · rcases p14155_3 (m.d 3 4) (by simp) with h14166 | h14166
                                                · linarith only [h13988, h14166, hlam]
                                                · linarith only [h12236, h14166, hlam]
                                            · linarith only [h10472, h14163, hlam]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h12236, h13984, h13988, h13991, h13995, hlam, p14155_2]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h10472, h12236, hc01, hc13, hlam, hphi, p14155_1]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h10472, h13923, h13985, hc01, hc12, hlam, hphi, p14155_1]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h12233, hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h13985, hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h13991, hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h13993, hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h10472, h13985, h13988, hc01, hc12, hlam, hphi, p14155_1]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h13988, hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          rcases p14155_3 (m.d 0 3) (by simp) with h14181 | h14181
                                          · linarith only [h12236, h14181, hlam]
                                          · linarith only [h12233, h14181, hlam]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h10472, h13923, h13985, h13988, hc01, hc12, hlam, hphi, p14155_1]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h10472, h13985, h13989, hc01, hc12, hlam, hphi, p14155_1]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h13989, hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          rcases p14155_3 (m.d 0 3) (by simp) with h14188 | h14188
                                          · linarith only [h13923, h14188, hlam]
                                          · linarith only [h12233, h14188, hlam]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [h14102, hlam, p14155_0]
                                        · have p14155_0 := h14155c.1
                                          have p14155_1 := h14155c.2.1
                                          have p14155_2 := h14155c.2.2.1
                                          have p14155_3 := h14155c.2.2.2
                                          linarith only [hlam, p14155_0]
                                      · linarith only [h12236, h13984, h13985, h13988, h13991, h13995, h14154, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                      · linarith only [h12236, h13984, h13988, h13991, h13995, h14154, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                      · linarith only [h11379, h14154, hc01, hlam]
                                      · linarith only [h14154, hc01, hlam, p14103_1]
                                    · linarith only [h14153, hlam, p14103_0]
                                  · linarith only [h11379, h14152, hlam]
                                · linarith only [h10472, h14151, hlam]
                              · linarith only [h0, h14150, hlam]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h13987, hlam, p14103_1]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h13989, hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [h13990, hlam, p14103_0]
                          · have p14103_0 := h14103c.1
                            have p14103_1 := h14103c.2.1
                            have p14103_2 := h14103c.2.2.1
                            have p14103_3 := h14103c.2.2.2
                            linarith only [hlam, p14103_0]
                        · linarith only [h12236, h13984, h14102, hlam]
                · linarith only [h11379, h12236, h13984, h13985, h13988, h13990, hc01, hc12, hlam, hphi]
              · linarith only [h12236, h13984, h13988, h13989, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14208 | h14208
              · linarith only [h10472, h13923, h13988, h14208, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14210 | h14210
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14211 | h14211
                  · linarith only [h10472, h13988, h14211, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14213 | h14213
                    · linarith only [h0, h12013, h12233, h14208, h14213, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14215 | h14215
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14216 | h14216
                        · rcases h1bigk with h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [hlam, p14217_0]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h0, hlam, p14217_0]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h10472, hlam, p14217_0]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h11379, hlam, p14217_0]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h12013, hlam, p14217_0]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            rcases p14217_3 (m.d 0 1) (by simp) with h14223 | h14223
                            · linarith only [h14223, hlam, p14217_0]
                            · rcases p14217_3 (m.d 1 2) (by simp) with h14225 | h14225
                              · rcases p14217_3 (m.d 1 3) (by simp) with h14226 | h14226
                                · linarith only [h13985, h14226, hlam]
                                · linarith only [h10472, h14226, hlam]
                              · linarith only [h14225, hlam, p14217_0]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [hlam, p14217_0]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h10472, hc01, hc12, hlam, hphi, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h11379, hc01, hc12, hlam, hphi, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h12013, hc01, hc12, hlam, hphi, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h14208, h14216, hc01, hc34, hlam, hphi, ht12, ht23, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h13985, hlam, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [hlam, p14217_0]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h13988, hlam, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h14208, hlam, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            rcases p14217_3 (m.d 0 1) (by simp) with h14239 | h14239
                            · linarith only [h14239, hlam, p14217_0]
                            · rcases p14217_3 (m.d 1 2) (by simp) with h14241 | h14241
                              · rcases p14217_3 (m.d 1 3) (by simp) with h14242 | h14242
                                · linarith only [h13988, h14242, hlam]
                                · linarith only [h10472, h14242, hlam]
                              · linarith only [h0, h14241, hlam]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h13986, hlam, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h10472, hc01, hc14, hlam, hphi, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [hlam, p14217_0]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h10472, h13988, h14208, hc01, hc34, hlam, hphi, ht12, ht23, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            rcases p14217_3 (m.d 0 1) (by simp) with h14250 | h14250
                            · linarith only [h14250, hlam, p14217_0]
                            · rcases p14217_3 (m.d 1 2) (by simp) with h14252 | h14252
                              · rcases p14217_3 (m.d 1 3) (by simp) with h14253 | h14253
                                · linarith only [h14208, h14253, hlam]
                                · linarith only [h10472, h14253, hlam]
                              · linarith only [h0, h14252, hlam]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h13987, hlam, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h10472, hc01, hc15, hlam, hphi, p14217_1]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [h14210, hlam, p14217_0]
                          · have p14217_0 := h14217c.1
                            have p14217_1 := h14217c.2.1
                            have p14217_2 := h14217c.2.2.1
                            have p14217_3 := h14217c.2.2.2
                            linarith only [hlam, p14217_0]
                        · linarith only [h11379, h13988, h14215, h14216, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14262 | h14262
                        · rcases h1bigk with h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c | h14263c
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [hlam, p14263_0]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h0, hlam, p14263_0]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h10472, hlam, p14263_0]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h11379, hlam, p14263_0]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h12013, hlam, p14263_0]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            rcases p14263_3 (m.d 0 1) (by simp) with h14269 | h14269
                            · linarith only [h14269, hlam, p14263_0]
                            · rcases p14263_3 (m.d 1 2) (by simp) with h14271 | h14271
                              · rcases p14263_3 (m.d 1 3) (by simp) with h14272 | h14272
                                · linarith only [h13985, h14272, hlam]
                                · linarith only [h10472, h14272, hlam]
                              · linarith only [h14271, hlam, p14263_0]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [hlam, p14263_0]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h10472, hc01, hc12, hlam, hphi, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h11379, hc01, hc12, hlam, hphi, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h12013, hc01, hc12, hlam, hphi, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h14208, hc01, hc35, hlam, hphi, ht12, ht23, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h13985, hlam, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [hlam, p14263_0]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h13988, hlam, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h14208, hlam, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            rcases p14263_3 (m.d 0 1) (by simp) with h14285 | h14285
                            · linarith only [h14285, hlam, p14263_0]
                            · rcases p14263_3 (m.d 1 2) (by simp) with h14287 | h14287
                              · rcases p14263_3 (m.d 1 3) (by simp) with h14288 | h14288
                                · linarith only [h13988, h14288, hlam]
                                · linarith only [h10472, h14288, hlam]
                              · linarith only [h0, h14287, hlam]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h13986, hlam, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h10472, hc01, hc14, hlam, hphi, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [hlam, p14263_0]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h12013, h13984, h13988, h14211, h14215, hc23, hc34, hlam, hphi, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            rcases p14263_3 (m.d 0 1) (by simp) with h14296 | h14296
                            · linarith only [h14296, hlam, p14263_0]
                            · rcases p14263_3 (m.d 1 2) (by simp) with h14298 | h14298
                              · rcases p14263_3 (m.d 1 3) (by simp) with h14299 | h14299
                                · linarith only [h14208, h14299, hlam]
                                · linarith only [h10472, h14299, hlam]
                              · linarith only [h0, h14298, hlam]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h13987, hlam, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h10472, hc01, hc15, hlam, hphi, p14263_1]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [h14210, hlam, p14263_0]
                          · have p14263_0 := h14263c.1
                            have p14263_1 := h14263c.2.1
                            have p14263_2 := h14263c.2.2.1
                            have p14263_3 := h14263c.2.2.2
                            linarith only [hlam, p14263_0]
                        · linarith only [h11379, h13984, h13988, h14262, hlam]
                · linarith only [h11379, h13984, h14210, hlam]
          · linarith only [h0, h12235, h13987, hlam]
        · linarith only [h0, h12234, h13986, hlam]
      · linarith only [h0, h12233, h13985, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h14312 | h14312
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14313 | h14313
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14314 | h14314
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14315 | h14315
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14316 | h14316
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14317 | h14317
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14318 | h14318
                  · linarith only [h12233, h12236, h14318, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14320 | h14320
                    · linarith only [h12233, h13923, h14320, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14322 | h14322
                      · linarith only [h12234, h13984, h14322, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14324 | h14324
                        · linarith only [h10472, h12236, h13984, h14312, h14315, h14324, hc01, hc12, hlam, hphi]
                        · linarith only [h10472, h12236, h14317, h14324, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14327 | h14327
                  · linarith only [h12233, h12236, h14327, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14329 | h14329
                    · linarith only [h12233, h13923, h14329, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14331 | h14331
                      · linarith only [h11379, h14317, h14331, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14333 | h14333
                        · linarith only [h14315, h14317, h14333, hlam]
                        · rcases h1bigk with h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c | h14335c
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h0, hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h10472, hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h11379, hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h12013, hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            rcases p14335_3 (m.d 0 1) (by simp) with h14341 | h14341
                            · linarith only [h14341, hlam, p14335_0]
                            · rcases p14335_3 (m.d 1 2) (by simp) with h14343 | h14343
                              · rcases p14335_3 (m.d 1 3) (by simp) with h14344 | h14344
                                · linarith only [h14312, h14344, hlam]
                                · linarith only [h10472, h14344, hlam]
                              · linarith only [h14343, hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h10472, hc01, hc12, hlam, hphi, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h11379, hc01, hc12, hlam, hphi, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h12013, hc01, hc12, hlam, hphi, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            rcases p14335_3 (m.d 0 1) (by simp) with h14352 | h14352
                            · linarith only [h14352, hlam, p14335_0]
                            · rcases p14335_3 (m.d 1 2) (by simp) with h14354 | h14354
                              · rcases p14335_3 (m.d 1 3) (by simp) with h14355 | h14355
                                · rcases p14335_3 (m.d 1 4) (by simp) with h14356 | h14356
                                  · linarith only [h14315, h14356, hlam]
                                  · linarith only [h11379, h14356, hlam]
                                · linarith only [h14355, hlam, p14335_0]
                              · linarith only [h0, h14354, hlam]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h14312, hlam, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h10472, h12236, h14315, hc01, hc13, hlam, hphi, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h12013, h14312, hc01, hc12, hlam, hphi, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h14317, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h14313, hlam, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h14315, hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h14317, hlam, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            rcases p14335_3 (m.d 0 1) (by simp) with h14370 | h14370
                            · linarith only [h14370, hlam, p14335_0]
                            · rcases p14335_3 (m.d 1 2) (by simp) with h14372 | h14372
                              · rcases p14335_3 (m.d 1 3) (by simp) with h14373 | h14373
                                · rcases p14335_3 (m.d 1 4) (by simp) with h14374 | h14374
                                  · linarith only [h14317, h14374, hlam]
                                  · linarith only [h11379, h14374, hlam]
                                · linarith only [h10472, h14373, hlam]
                              · linarith only [h0, h14372, hlam]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h14314, hlam, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h14316, hlam, p14335_0]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [h11379, hc01, hc15, hlam, hphi, p14335_1]
                          · have p14335_0 := h14335c.1
                            have p14335_1 := h14335c.2.1
                            have p14335_2 := h14335c.2.2.1
                            have p14335_3 := h14335c.2.2.2
                            linarith only [hlam, p14335_0]
              · linarith only [h10472, h12236, h14315, h14316, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14384 | h14384
              · linarith only [h10472, h13923, h14315, h14384, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14386 | h14386
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14387 | h14387
                  · linarith only [h10472, h14315, h14387, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14389 | h14389
                    · linarith only [h12233, h12236, h13984, h14386, h14389, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14391 | h14391
                      · linarith only [h0, h10472, h12234, h12236, h13984, h14391, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14393 | h14393
                        · rcases h1bigk with h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c | h14394c
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [hlam, p14394_0]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h0, hlam, p14394_0]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h10472, hlam, p14394_0]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h11379, hlam, p14394_0]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h12013, hlam, p14394_0]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            rcases p14394_3 (m.d 0 1) (by simp) with h14400 | h14400
                            · linarith only [h14400, hlam, p14394_0]
                            · rcases p14394_3 (m.d 1 2) (by simp) with h14402 | h14402
                              · rcases p14394_3 (m.d 1 3) (by simp) with h14403 | h14403
                                · linarith only [h14312, h14403, hlam]
                                · linarith only [h10472, h14403, hlam]
                              · linarith only [h14402, hlam, p14394_0]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [hlam, p14394_0]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h10472, hc01, hc12, hlam, hphi, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h13984, h14386, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h12013, hc01, hc12, hlam, hphi, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h14315, hc01, hc34, hlam, hphi, ht12, ht23, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h14312, hlam, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [hlam, p14394_0]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h14315, hlam, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h14384, hlam, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            rcases p14394_3 (m.d 0 1) (by simp) with h14416 | h14416
                            · linarith only [h14416, hlam, p14394_0]
                            · rcases p14394_3 (m.d 1 2) (by simp) with h14418 | h14418
                              · rcases p14394_3 (m.d 1 3) (by simp) with h14419 | h14419
                                · linarith only [h14315, h14419, hlam]
                                · linarith only [h10472, h14419, hlam]
                              · linarith only [h0, h14418, hlam]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h14313, hlam, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h10472, hc01, hc14, hlam, hphi, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [hlam, p14394_0]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h10472, h12236, h13984, h14315, h14386, hc01, hc34, hlam, hphi, ht12, ht23, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            rcases p14394_3 (m.d 0 1) (by simp) with h14427 | h14427
                            · linarith only [h14427, hlam, p14394_0]
                            · rcases p14394_3 (m.d 1 2) (by simp) with h14429 | h14429
                              · rcases p14394_3 (m.d 1 3) (by simp) with h14430 | h14430
                                · linarith only [h14384, h14430, hlam]
                                · linarith only [h10472, h14430, hlam]
                              · linarith only [h0, h14429, hlam]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h14314, hlam, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h10472, hc01, hc15, hlam, hphi, p14394_1]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [h14386, hlam, p14394_0]
                          · have p14394_0 := h14394c.1
                            have p14394_1 := h14394c.2.1
                            have p14394_2 := h14394c.2.2.1
                            have p14394_3 := h14394c.2.2.2
                            linarith only [hlam, p14394_0]
                        · linarith only [h10472, h14315, h14393, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14439 | h14439
                  · linarith only [h10472, h14315, h14439, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14441 | h14441
                    · linarith only [h12233, h13923, h14441, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14443 | h14443
                      · linarith only [h0, h10472, h12234, h12236, h13984, h14443, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14445 | h14445
                        · linarith only [h10472, h14315, h14386, h14445, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h10472, h14315, h14445, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h12235, h14314, hlam]
        · linarith only [h0, h12234, h14313, hlam]
      · linarith only [h0, h12233, h14312, hlam]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 0 3 4 (by decide) (by decide) with h12236 | h12236
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 0 3 4 (by decide) (by decide) with h14451 | h14451
  · rcases m.htr 0 3 5 (by decide) (by decide) with h14452 | h14452
    · linarith only [h12233, h12235, h14452, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h14454 | h14454
      · linarith only [h12234, h12235, h14454, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h14456 | h14456
        · rcases m.htr 1 2 4 (by decide) (by decide) with h14457 | h14457
          · rcases m.htr 1 2 5 (by decide) (by decide) with h14458 | h14458
            · rcases m.htr 1 3 4 (by decide) (by decide) with h14459 | h14459
              · rcases m.htr 1 3 5 (by decide) (by decide) with h14460 | h14460
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14461 | h14461
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14462 | h14462
                    · linarith only [h12233, h12235, h14458, h14462, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h12233, h12235, h14451, h14458, h14462, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14465 | h14465
                    · linarith only [h12233, h12235, h14458, h14465, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h12233, h12235, h14451, h14458, h14465, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14468 | h14468
                  · linarith only [h11379, h14454, h14459, h14460, h14468, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14470 | h14470
                    · linarith only [h12233, h12235, h14458, h14470, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h12233, h12235, h14451, h14458, h14470, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h10472, h12233, h12235, h14451, h14458, h14459, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h14474 | h14474
              · rcases m.htr 1 3 5 (by decide) (by decide) with h14475 | h14475
                · linarith only [h14451, h14452, h14456, h14458, h14475, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14477 | h14477
                  · linarith only [h11379, h14454, h14457, h14458, h14477, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14479 | h14479
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14480 | h14480
                      · linarith only [h0, h12233, h14458, h14475, h14480, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14482 | h14482
                        · linarith only [h0, h12234, h14458, h14480, h14482, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h0, h12233, h14458, h14479, h14482, hc34, hc45, hlam, hphi]
                    · linarith only [h14451, h14452, h14479, hc23, hc35, hlam, hphi]
              · linarith only [h10472, h14451, h14474, hlam]
          · linarith only [h0, h12234, h14457, hlam]
        · linarith only [h0, h12233, h14456, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h14489 | h14489
    · linarith only [h12234, h12235, h14451, h14489, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h14491 | h14491
      · linarith only [h12234, h12235, h14491, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h14493 | h14493
        · rcases m.htr 1 2 4 (by decide) (by decide) with h14494 | h14494
          · rcases m.htr 1 2 5 (by decide) (by decide) with h14495 | h14495
            · rcases m.htr 1 3 4 (by decide) (by decide) with h14496 | h14496
              · rcases m.htr 1 3 5 (by decide) (by decide) with h14497 | h14497
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14498 | h14498
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14499 | h14499
                    · linarith only [h12233, h12235, h14451, h14499, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14501 | h14501
                      · linarith only [h12234, h12235, h14489, h14495, h14499, h14501, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14503 | h14503
                        · linarith only [h12234, h12235, h14493, h14497, h14501, h14503, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14505 | h14505
                          · linarith only [h12234, h12235, h14499, h14503, h14505, hc23, hc34, hlam, hphi]
                          · linarith only [h10472, h14451, h14493, h14496, h14498, h14505, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14508 | h14508
                    · linarith only [h10472, h12233, h12235, h14451, h14508, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14510 | h14510
                      · linarith only [h12234, h12235, h14489, h14495, h14508, h14510, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14512 | h14512
                        · linarith only [h12234, h12235, h14493, h14497, h14498, h14510, h14512, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14514 | h14514
                          · linarith only [h14496, h14498, h14514, hlam]
                          · rcases h1bigk with h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c | h14516c
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h0, hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h10472, hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h11379, hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h12013, hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              rcases p14516_3 (m.d 0 1) (by simp) with h14522 | h14522
                              · linarith only [h14522, hlam, p14516_0]
                              · rcases p14516_3 (m.d 1 2) (by simp) with h14524 | h14524
                                · rcases p14516_3 (m.d 1 3) (by simp) with h14525 | h14525
                                  · linarith only [h14493, h14525, hlam]
                                  · linarith only [h10472, h14525, hlam]
                                · linarith only [h14524, hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h12235, h14497, h14510, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h10472, h14451, h14496, hc01, hc12, hlam, hphi, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h12013, hc01, hc12, hlam, hphi, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              rcases p14516_3 (m.d 0 1) (by simp) with h14533 | h14533
                              · linarith only [h14533, hlam, p14516_0]
                              · rcases p14516_3 (m.d 1 2) (by simp) with h14535 | h14535
                                · rcases p14516_3 (m.d 1 3) (by simp) with h14536 | h14536
                                  · rcases p14516_3 (m.d 1 4) (by simp) with h14537 | h14537
                                    · linarith only [h14496, h14537, hlam]
                                    · linarith only [h11379, h14537, hlam]
                                  · linarith only [h14536, hlam, p14516_0]
                                · linarith only [h0, h14535, hlam]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h14493, hlam, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h10472, h14451, h14496, hc01, hc13, hlam, hphi, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h12234, h12235, h14493, h14497, h14508, h14510, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h14498, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h14494, hlam, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h14496, hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h14498, hlam, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              rcases p14516_3 (m.d 0 1) (by simp) with h14551 | h14551
                              · linarith only [h14551, hlam, p14516_0]
                              · rcases p14516_3 (m.d 1 2) (by simp) with h14553 | h14553
                                · rcases p14516_3 (m.d 1 3) (by simp) with h14554 | h14554
                                  · rcases p14516_3 (m.d 1 4) (by simp) with h14555 | h14555
                                    · linarith only [h14498, h14555, hlam]
                                    · linarith only [h11379, h14555, hlam]
                                  · linarith only [h10472, h14554, hlam]
                                · linarith only [h0, h14553, hlam]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h14495, hlam, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h14497, hlam, p14516_0]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [h11379, hc01, hc15, hlam, hphi, p14516_1]
                            · have p14516_0 := h14516c.1
                              have p14516_1 := h14516c.2.1
                              have p14516_2 := h14516c.2.2.1
                              have p14516_3 := h14516c.2.2.2
                              linarith only [hlam, p14516_0]
                · linarith only [h10472, h14451, h14496, h14497, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h14565 | h14565
                · linarith only [h10472, h14489, h14496, h14565, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14567 | h14567
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14568 | h14568
                    · linarith only [h10472, h14496, h14568, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14570 | h14570
                      · linarith only [h12234, h12235, h14495, h14568, h14570, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14572 | h14572
                        · linarith only [h10472, h12234, h12235, h14451, h14491, h14495, h14572, hc01, hc12, hlam, hphi]
                        · linarith only [h12234, h12235, h14496, h14567, h14568, h14572, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14575 | h14575
                    · linarith only [h12233, h12235, h14495, h14575, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14577 | h14577
                      · linarith only [h12234, h12235, h14495, h14565, h14575, h14577, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14579 | h14579
                        · linarith only [h12234, h12235, h14495, h14567, h14579, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14581 | h14581
                          · linarith only [h10472, h14496, h14567, h14581, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h10472, h14496, h14581, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h14584 | h14584
              · linarith only [h10472, h14451, h14493, h14495, h14584, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h14586 | h14586
                · linarith only [h10472, h14489, h14494, h14495, h14584, h14586, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14588 | h14588
                  · linarith only [h10472, h14451, h14491, h14494, h14495, h14588, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14590 | h14590
                    · linarith only [h10472, h14584, h14590, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14592 | h14592
                      · linarith only [h0, h12234, h14495, h14586, h14590, h14592, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14594 | h14594
                        · linarith only [h0, h12234, h14495, h14594, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14596 | h14596
                          · linarith only [h0, h14495, h14594, h14596, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h10472, h14584, h14596, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h12234, h14494, hlam]
        · linarith only [h0, h12233, h14493, hlam]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 0 2 5 (by decide) (by decide) with h12235 | h12235
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235

end R2N4
