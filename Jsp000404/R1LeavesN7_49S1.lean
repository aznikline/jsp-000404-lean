import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_49S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h949 | h949
  · rcases m.htr 0 3 4 (by decide) (by decide) with h950 | h950
    · linarith only [h4, h5, h950, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h952 | h952
      · rcases m.htr 0 4 5 (by decide) (by decide) with h953 | h953
        · rcases m.htr 1 2 3 (by decide) (by decide) with h954 | h954
          · rcases m.htr 1 2 4 (by decide) (by decide) with h955 | h955
            · linarith only [h5, h949, h955, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h957 | h957
              · rcases m.htr 1 3 4 (by decide) (by decide) with h958 | h958
                · linarith only [h0, h950, h952, h954, h958, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h960 | h960
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h961 | h961
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h962 | h962
                      · linarith only [h2, h950, h954, h955, h962, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h964 | h964
                        · linarith only [h0, h5, h954, h962, h964, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h1, h4, h5, h960, h962, h964, hc23, hc34, hlam, hphi]
                    · linarith only [h5, h953, h955, h961, hc24, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h950, h952, h960, hc34, hlam, hphi, ht12, ht23, u1ehi2]
              · linarith only [h5, h949, h957, hc12, hc24, hlam, hphi]
          · linarith only [h4, h5, h954, hc24, hlam, hphi, ht12, u1ehi1]
        · linarith only [h5, h949, h953, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h972 | h972
        · rcases m.htr 1 2 3 (by decide) (by decide) with h973 | h973
          · rcases m.htr 1 2 4 (by decide) (by decide) with h974 | h974
            · linarith only [h5, h949, h974, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h976 | h976
              · rcases m.htr 1 3 4 (by decide) (by decide) with h977 | h977
                · linarith only [h1, h2, h950, h952, h974, h976, h977, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h979 | h979
                  · linarith only [h1, h952, h979, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h981 | h981
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h982 | h982
                      · linarith only [h1, h950, h973, h982, hc12, hlam, hphi, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h984 | h984
                        · linarith only [h0, h1, h5, h952, h973, h982, h984, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h986 | h986
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h987 | h987
                            · rcases h2bigk with h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h5, h982, hc12, hc34, hlam, hphi, ht23, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h5, h982, hc23, hc34, hlam, hphi, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h5, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h5, h982, h986, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p988_1, u5ehi4]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, h5, h982, hc23, hc34, hlam, hphi, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h974, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, h5, h982, h986, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p988_1, u5ehi4]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h4, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h973, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h982, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h984, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, h982, hc34, hlam, hphi, ht12, ht23, p988_1, u1ehi1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h973, h982, hc34, hlam, hphi, ht12, ht23, p988_1, u1ehi2]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                rcases p988_3 (m.d 0 2) (by simp) with h1006 | h1006
                                · linarith only [h1006, h5, hlam]
                                · linarith only [h1006, h4, hlam]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                rcases p988_3 (m.d 0 2) (by simp) with h1010 | h1010
                                · linarith only [h1010, h5, hlam]
                                · linarith only [h1010, h949, hlam]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h949, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h976, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, h976, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h986, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                            · linarith only [h0, h5, h976, h982, h986, h987, hlam]
                          · linarith only [h0, h5, h976, h986, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · linarith only [h950, h972, h981, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h5, h949, h976, hc24, hlam, hphi, ht12, u1ehi1]
          · linarith only [h4, h5, h973, hc24, hlam, hphi, ht12, u1ehi1]
        · linarith only [h5, h949, h972, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1024 | h1024
    · linarith only [h1024, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1026 | h1026
      · linarith only [h1026, h4, h949, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1028 | h1028
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1029 | h1029
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1030 | h1030
            · linarith only [h0, h1030, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1032 | h1032
              · linarith only [h1, h1032, h4, h949, hc12, hlam, hphi, u1ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1034 | h1034
                · linarith only [h1, h1024, h1034, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1036 | h1036
                  · linarith only [h1, h1026, h1036, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1038 | h1038
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1039 | h1039
                      · linarith only [h1, h1024, h1039, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1041 | h1041
                        · linarith only [h0, h1, h1026, h1029, h1041, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1043 | h1043
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1044 | h1044
                            · rcases h2bigk with h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [hlam, p1045_0]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1039, h1043, h949, hc12, hc34, hlam, hphi, ht23, p1045_1]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1039, h1043, h949, hc23, hc34, hlam, hphi, p1045_1]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h5, hlam, p1045_0]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h949, hlam, p1045_0]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h0, hlam, p1045_1]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [hlam, p1045_0]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h0, h1039, h1043, h949, hc23, hc34, hlam, hphi, p1045_1]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1030, hlam, p1045_0]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1032, hlam, p1045_0]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h4, hlam, p1045_0]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1029, hlam, p1045_0]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [hlam, p1045_0]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1039, hlam, p1045_1]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1041, hlam, p1045_1]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h0, h1039, hc34, hlam, hphi, ht12, ht23, p1045_1, u1ehi1]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1029, h1039, hc34, hlam, hphi, ht12, ht23, p1045_1, u1ehi2]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                rcases p1045_3 (m.d 0 2) (by simp) with h1063 | h1063
                                · linarith only [h1063, h5, hlam]
                                · linarith only [h1063, h4, hlam]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [hlam, p1045_0]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1, h1039, h4, h949, hc34, hlam, hphi, ht12, ht23, p1045_1, u1ehi2]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1, h4, hc25, hlam, hphi, ht12, p1045_1, u1ehi2]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1029, hc25, hlam, hphi, ht12, p1045_1, u1ehi2]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                rcases p1045_3 (m.d 0 2) (by simp) with h1070 | h1070
                                · linarith only [h1070, h949, hlam]
                                · linarith only [h1070, h4, hlam]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [h1043, hlam, p1045_1]
                              · have p1045_0 := h1045c.1
                                have p1045_1 := h1045c.2.1
                                have p1045_2 := h1045c.2.2.1
                                have p1045_3 := h1045c.2.2.2
                                linarith only [hlam, p1045_0]
                            · linarith only [h1, h1039, h1044, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                          · linarith only [h1028, h1038, h1043, h2, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · linarith only [h1028, h1038, h5, hc24, hlam, hphi, ht12, u1ehi3]
          · linarith only [h1029, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1079 | h1079
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1080 | h1080
            · linarith only [h0, h1080, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1082 | h1082
              · linarith only [h0, h1082, h3, h5, h949, hc24, hlam, hphi, ht12, u1ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1084 | h1084
                · linarith only [h1, h1024, h1084, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1086 | h1086
                  · linarith only [h1, h1026, h1086, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1088 | h1088
                    · linarith only [h0, h1028, h1088, h2, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1090 | h1090
                      · linarith only [h1, h1024, h1090, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1092 | h1092
                        · linarith only [h1, h1026, h1079, h1092, hc12, hlam, hphi, u1ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1094 | h1094
                          · linarith only [h1, h1028, h1094, h4, h5, hc24, hlam, hphi, ht12, u1ehi2]
                          · linarith only [h1, h1094, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · linarith only [h1079, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1098 | h1098
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1099 | h1099
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1100 | h1100
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1101 | h1101
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1102 | h1102
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1103 | h1103
            · linarith only [h1098, h1102, h1103, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1105 | h1105
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1106 | h1106
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1107 | h1107
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1108 | h1108
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1109 | h1109
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1110 | h1110
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1111 | h1111
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1112 | h1112
                            · linarith only [h0, h1105, h1112, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1114 | h1114
                              · linarith only [h1110, h1112, h1114, hlam]
                              · rcases h2bigk with h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h4, hc12, hc23, hlam, hphi, p1116_1]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h4, hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  rcases p1116_3 (m.d 0 2) (by simp) with h1120 | h1120
                                  · rcases p1116_3 (m.d 1 2) (by simp) with h1121 | h1121
                                    · linarith only [h0, h1121, hlam]
                                    · linarith only [h1105, h1121, hlam]
                                  · linarith only [h1120, hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1116_1, u5ehi2]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h0, hlam, p1116_1]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h1103, hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  rcases p1116_3 (m.d 0 2) (by simp) with h1129 | h1129
                                  · rcases p1116_3 (m.d 1 2) (by simp) with h1130 | h1130
                                    · rcases p1116_3 (m.d 2 3) (by simp) with h1131 | h1131
                                      · rcases p1116_3 (m.d 2 4) (by simp) with h1132 | h1132
                                        · linarith only [h1132, hlam, p1116_0]
                                        · rcases p1116_3 (m.d 2 5) (by simp) with h1134 | h1134
                                          · linarith only [h1106, h1134, hlam]
                                          · linarith only [h1112, h1134, hlam]
                                      · linarith only [h1110, h1131, hlam]
                                    · linarith only [h1130, hlam, p1116_0]
                                  · linarith only [h1098, h1129, hlam]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h0, h1111, hc01, hlam, hphi, ht0b, ht5b, p1116_1, u5ehi3]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p1116_1, u1ehi1]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p1116_1, u1ehi1]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h1098, h1109, h1112, h2, h4, hlam, p1116_2]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  rcases p1116_3 (m.d 0 2) (by simp) with h1145 | h1145
                                  · linarith only [h1145, h4, hlam]
                                  · linarith only [h1099, h1145, hlam]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h1098, hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h1105, hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h1110, hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h1112, hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h1099, hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h1106, hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h1111, hlam, p1116_0]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [h1099, h1110, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1116_1]
                                · have p1116_0 := h1116c.1
                                  have p1116_1 := h1116c.2.1
                                  have p1116_2 := h1116c.2.2.1
                                  have p1116_3 := h1116c.2.2.2
                                  linarith only [hlam, p1116_0]
                          · linarith only [h0, h1106, h1111, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h1105, h1109, h1110, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h1098, h1102, h1109, h4, hc23, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h1101, h1103, h1106, h1108, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · linarith only [h1100, h1103, h1106, h1107, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h1099, h1106, h4, hc12, hc23, hlam, hphi]
              · linarith only [h1098, h1105, h4, hc23, hlam, hphi, ht12, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1165 | h1165
            · linarith only [h1099, h1165, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1167 | h1167
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1168 | h1168
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1169 | h1169
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1170 | h1170
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1171 | h1171
                      · linarith only [h1102, h1171, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1173 | h1173
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1174 | h1174
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1175 | h1175
                            · linarith only [h0, h1102, h1167, h1175, h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1177 | h1177
                              · linarith only [h0, h1102, h1168, h1173, h1175, h1177, h2, h4, hc23, hlam, hphi, ht12, u1ehi3]
                              · rcases h2bigk with h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h4, hc12, hc23, hlam, hphi, p1179_1]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h4, hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  rcases p1179_3 (m.d 0 2) (by simp) with h1183 | h1183
                                  · rcases p1179_3 (m.d 1 2) (by simp) with h1184 | h1184
                                    · linarith only [h0, h1184, hlam]
                                    · linarith only [h1167, h1184, hlam]
                                  · linarith only [h1183, hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h1174, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1179_1, u5ehi3]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h0, hlam, p1179_1]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h1165, hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  rcases p1179_3 (m.d 0 2) (by simp) with h1192 | h1192
                                  · rcases p1179_3 (m.d 1 2) (by simp) with h1193 | h1193
                                    · rcases p1179_3 (m.d 2 3) (by simp) with h1194 | h1194
                                      · rcases p1179_3 (m.d 2 4) (by simp) with h1195 | h1195
                                        · linarith only [h1195, hlam, p1179_0]
                                        · rcases p1179_3 (m.d 2 5) (by simp) with h1197 | h1197
                                          · linarith only [h1168, h1197, hlam]
                                          · linarith only [h1175, h1197, hlam]
                                      · linarith only [h1173, h1194, hlam]
                                    · linarith only [h1193, hlam, p1179_0]
                                  · linarith only [h1098, h1192, hlam]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h0, h1174, hc01, hlam, hphi, ht0b, ht5b, p1179_1, u5ehi3]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p1179_1, u1ehi1]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p1179_1, u1ehi1]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  rcases p1179_3 (m.d 0 2) (by simp) with h1207 | h1207
                                  · linarith only [h1207, h4, hlam]
                                  · linarith only [h1098, h1207, hlam]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  rcases p1179_3 (m.d 0 2) (by simp) with h1210 | h1210
                                  · linarith only [h1210, h4, hlam]
                                  · linarith only [h1099, h1210, hlam]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h1098, hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h1167, hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h1173, hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h1175, hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h1099, hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h1168, hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h1174, hlam, p1179_0]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [h0, h1168, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1179_1]
                                · have p1179_0 := h1179c.1
                                  have p1179_1 := h1179c.2.1
                                  have p1179_2 := h1179c.2.2.1
                                  have p1179_3 := h1179c.2.2.2
                                  linarith only [hlam, p1179_0]
                          · linarith only [h0, h1168, h1174, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h1168, h1173, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h1101, h1170, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h1100, h1165, h1168, h1169, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h1099, h1168, h4, hc23, hlam, hphi, ht12, u1ehi1]
              · linarith only [h1098, h1167, h4, hc23, hlam, hphi, ht12, u1ehi1]
        · linarith only [h1099, h1101, h4, hlam]
      · linarith only [h1098, h1100, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1231 | h1231
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1232 | h1232
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1233 | h1233
          · linarith only [h1098, h1099, h1233, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1235 | h1235
            · linarith only [h0, h1235, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1237 | h1237
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1238 | h1238
                · linarith only [h0, h1099, h1238, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1240 | h1240
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1241 | h1241
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1242 | h1242
                      · linarith only [h1233, h1242, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1244 | h1244
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1245 | h1245
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1246 | h1246
                            · linarith only [h0, h1233, h1237, h1246, h2, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1248 | h1248
                              · linarith only [h0, h1099, h1237, h1244, h1246, h1248, hlam]
                              · rcases h2bigk with h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1099, h1246, hc12, hc45, hlam, hphi, ht23, ht34, p1250_1]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h4, hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1099, h1244, h1246, hc34, hc45, hlam, hphi, p1250_1]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1099, hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h0, hlam, p1250_1]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1235, hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h0, h1099, h1244, h1246, hc34, hc45, hlam, hphi, p1250_1]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1238, hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p1250_1, u1ehi1]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p1250_1, u1ehi1]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  rcases p1250_3 (m.d 0 2) (by simp) with h1264 | h1264
                                  · linarith only [h1264, h4, hlam]
                                  · linarith only [h1098, h1264, hlam]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1098, h1099, h2, hc23, hlam, hphi, ht12, p1250_1, u1ehi3]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1098, hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1237, hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1244, hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1246, hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1098, h2, hc25, hlam, hphi, ht12, p1250_1, u1ehi3]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1237, hc25, hlam, hphi, ht12, p1250_1, u1ehi3]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [h1245, hlam, p1250_0]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  rcases p1250_3 (m.d 0 2) (by simp) with h1276 | h1276
                                  · linarith only [h1099, h1276, hlam]
                                  · linarith only [h1098, h1276, hlam]
                                · have p1250_0 := h1250c.1
                                  have p1250_1 := h1250c.2.1
                                  have p1250_2 := h1250c.2.2.1
                                  have p1250_3 := h1250c.2.2.2
                                  linarith only [hlam, p1250_0]
                          · linarith only [h1, h1098, h1241, h1245, h2, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                        · linarith only [h1098, h1244, h2, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · linarith only [h1232, h1241, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h1231, h1235, h1237, h1240, h4, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h1098, h1237, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1285 | h1285
          · linarith only [h1098, h1099, h1285, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1287 | h1287
            · linarith only [h0, h1098, h1287, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1289 | h1289
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1290 | h1290
                · linarith only [h1098, h1099, h1290, h2, hc12, hlam, hphi, u1ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1292 | h1292
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1293 | h1293
                    · linarith only [h1, h1232, h1293, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1295 | h1295
                      · linarith only [h1285, h1295, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1297 | h1297
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1298 | h1298
                          · linarith only [h1098, h1232, h1298, h2, h4, hc23, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h1098, h1298, h2, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h1098, h1297, h2, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h1231, h1292, h4, hc23, hlam, hphi, ht12, u1ehi2]
              · linarith only [h1098, h1289, h4, hc23, hlam, hphi, ht12, u1ehi1]
      · linarith only [h1098, h1231, h4, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1305 | h1305
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1306 | h1306
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1307 | h1307
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1308 | h1308
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1309 | h1309
            · linarith only [h1305, h1309, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1311 | h1311
              · linarith only [h1098, h1305, h1311, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1313 | h1313
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1314 | h1314
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1315 | h1315
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1316 | h1316
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1318 | h1318
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1319 | h1319
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1320 | h1320
                              · linarith only [h1, h1314, h1320, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases h2bigk with h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1098, h1313, h1317, h1319, h1320, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1322_1]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h4, hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1098, hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1098, h1317, h1319, h1320, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1322_1]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h0, hlam, p1322_1]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1309, hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1311, hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h0, h1319, h1320, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1322_1]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p1322_1, u1ehi1]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p1322_1, u1ehi1]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1098, h1305, h1319, h1320, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1322_1]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  rcases p1322_3 (m.d 0 2) (by simp) with h1337 | h1337
                                  · linarith only [h1337, h4, hlam]
                                  · linarith only [h1305, h1337, hlam]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h0, h1313, h1319, h1320, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1322_1]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1313, h1319, h1320, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1322_1]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1317, hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  rcases p1322_3 (m.d 0 2) (by simp) with h1344 | h1344
                                  · linarith only [h1098, h1344, hlam]
                                  · linarith only [h1305, h1344, hlam]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1305, hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1313, hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1318, hlam, p1322_0]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [h1319, hlam, p1322_1]
                                · have p1322_0 := h1322c.1
                                  have p1322_1 := h1322c.2.1
                                  have p1322_2 := h1322c.2.2.1
                                  have p1322_3 := h1322c.2.2.2
                                  linarith only [hlam, p1322_0]
                            · linarith only [h0, h1098, h1313, h1319, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                          · linarith only [h0, h1313, h1318, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h1313, h1317, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h1306, h1308, h1316, h4, hc23, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h1307, h1311, h1313, h1314, h1315, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · linarith only [h1306, h1314, h4, hc23, hlam, hphi, ht12, u1ehi2]
                · linarith only [h1098, h1305, h1313, hc24, hlam, hphi, ht12, u1ehi1]
          · linarith only [h1098, h1305, h1308, hlam]
        · linarith only [h1305, h1307, h4, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1361 | h1361
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1362 | h1362
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1363 | h1363
            · linarith only [h1305, h1363, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1365 | h1365
              · linarith only [h1098, h1305, h1365, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1367 | h1367
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1368 | h1368
                  · linarith only [h1, h1306, h1368, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1370 | h1370
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1371 | h1371
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1372 | h1372
                        · linarith only [h1, h1306, h1370, h1372, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h1367, h1372, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h1362, h1363, h1367, h1368, h1371, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · linarith only [h1361, h1363, h1367, h1370, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                · linarith only [h1305, h1306, h1367, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · linarith only [h1305, h1306, h1362, h4, hlam]
        · linarith only [h1305, h1361, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1380 | h1380
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1381 | h1381
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1382 | h1382
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1383 | h1383
            · linarith only [h0, h1383, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1385 | h1385
              · linarith only [h0, h1098, h1385, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1387 | h1387
                · linarith only [h0, h1305, h1387, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1389 | h1389
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1390 | h1390
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1391 | h1391
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1392 | h1392
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1393 | h1393
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1394 | h1394
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1395 | h1395
                              · linarith only [h1, h1389, h1395, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases h2bigk with h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c | h1397c
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h1305, h1394, hc24, hlam, hphi, ht12, p1397_1, u1ehi1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h4, hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h1098, hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h1305, hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h0, hlam, p1397_1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h1383, hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h1385, hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h1387, hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p1397_1, u1ehi1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p1397_1, u1ehi1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h0, h1098, hc23, hlam, hphi, ht12, p1397_1, u1ehi1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h0, h1305, hc23, hlam, hphi, ht12, p1397_1, u1ehi1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h0, hc24, hlam, hphi, ht12, p1397_1, u1ehi1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht12, p1397_1, u1ehi1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h1392, hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h0, h1305, h1392, hc23, hlam, hphi, ht12, p1397_1, u1ehi1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h0, hc25, hlam, hphi, ht12, p1397_1, u1ehi1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht12, p1397_1, u1ehi1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h1393, hlam, p1397_0]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [h1394, hlam, p1397_1]
                                · have p1397_0 := h1397c.1
                                  have p1397_1 := h1397c.2.1
                                  have p1397_2 := h1397c.2.2.1
                                  have p1397_3 := h1397c.2.2.2
                                  linarith only [hlam, p1397_0]
                            · linarith only [h0, h1098, h1391, h1394, h2, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                          · linarith only [h0, h1393, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h0, h1392, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h1380, h1382, h1391, h4, hc23, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h1381, h1390, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h1380, h1383, h1389, h4, hc23, hlam, hphi, ht12, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1429 | h1429
            · linarith only [h0, h1, h1098, h1429, h4, hc24, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1431 | h1431
              · linarith only [h0, h1098, h1431, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1433 | h1433
                · linarith only [h0, h1305, h1433, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1435 | h1435
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1436 | h1436
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1437 | h1437
                      · linarith only [h0, h1098, h1382, h1435, h1437, hc13, hlam, hphi, u1ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1439 | h1439
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1440 | h1440
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1441 | h1441
                            · linarith only [h0, h1098, h1382, h1441, hc24, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h0, h1098, h1441, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                          · linarith only [h1, h1436, h1440, h4, hlam]
                        · linarith only [h1, h1435, h1439, h4, hlam]
                    · linarith only [h1381, h1436, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h1380, h1429, h1435, h4, hc23, hlam, hphi, ht12, u1ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1448 | h1448
          · linarith only [h1380, h1381, h1448, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1450 | h1450
            · linarith only [h0, h1450, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1452 | h1452
              · linarith only [h0, h1098, h1452, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1454 | h1454
                · linarith only [h0, h1305, h1454, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1456 | h1456
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1457 | h1457
                    · linarith only [h1, h1381, h1457, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1459 | h1459
                      · linarith only [h1448, h1459, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1461 | h1461
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1462 | h1462
                          · linarith only [h1380, h1381, h1452, h1462, h2, hc23, hlam, hphi, ht12, u1ehi1]
                          · linarith only [h0, h1462, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h0, h1, h1456, h1461, h4, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                  · linarith only [h1380, h1381, h1456, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1467 | h1467
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1468 | h1468
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1469 | h1469
            · linarith only [h0, h1469, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1471 | h1471
              · linarith only [h0, h1098, h1471, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1473 | h1473
                · linarith only [h0, h1305, h1473, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1475 | h1475
                  · linarith only [h0, h1305, h1380, h1467, h1475, hc13, hlam, hphi, u1ehi1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1477 | h1477
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1478 | h1478
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1479 | h1479
                        · linarith only [h1, h1380, h1477, h1479, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h1479, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h1468, h1475, h1477, h1478, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h1467, h1477, h4, hc23, hlam, hphi, ht12, u1ehi2]
          · linarith only [h1380, h1467, h1468, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1485 | h1485
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1486 | h1486
            · linarith only [h0, h1486, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1488 | h1488
              · linarith only [h0, h1098, h1488, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1490 | h1490
                · linarith only [h0, h1305, h1490, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1492 | h1492
                  · linarith only [h1, h1380, h1492, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1494 | h1494
                    · linarith only [h1, h1467, h1494, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1496 | h1496
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1497 | h1497
                        · linarith only [h1, h1380, h1486, h1497, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h0, h1497, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h1098, h1485, h1496, hc24, hlam, hphi, ht12, u1ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1501 | h1501
            · linarith only [h0, h1501, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1503 | h1503
              · linarith only [h0, h1098, h1503, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1505 | h1505
                · linarith only [h0, h1305, h1505, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1507 | h1507
                  · linarith only [h1, h1380, h1507, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1509 | h1509
                    · linarith only [h1, h1467, h1509, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1511 | h1511
                      · linarith only [h1, h1380, h1485, h1511, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1513 | h1513
                        · linarith only [h0, h1380, h1513, h4, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h0, h1513, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0 m hb1 hb2 hb4 hb5 h0 h1
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x1 m hb1 hb2 hb4 hb5 h0 h1

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h1519, hc12, hlam, hphi, u1ehi2]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h1521, hc12, hlam, hphi, u1ehi3]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1523 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h1523, hc12, hlam, hphi, u1ehi4]

end R2N4
