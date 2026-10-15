import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10278000 in
set_option maxHeartbeats 10278000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h4129 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h6948 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  rcases m.htr 1 4 5 (by decide) (by decide) with h6949 | h6949
  · rcases m.htr 2 3 4 (by decide) (by decide) with h6950 | h6950
    · linarith only [h0, h4, h4129, h6948, h6950, hc01, hc35, hlam, hphi, ht0b, ht5b]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h6952 | h6952
      · rcases m.htr 2 4 5 (by decide) (by decide) with h6953 | h6953
        · rcases m.htr 3 4 5 (by decide) (by decide) with h6954 | h6954
          · rcases h1bigk with h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c | h6955c
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h0, h10, h4, h6950, h7, hlam, p6955_2]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              rcases p6955_3 (m.d 0 1) (by simp) with h6958 | h6958
              · rcases p6955_3 (m.d 1 2) (by simp) with h6959 | h6959
                · linarith only [h0, h6959, hlam]
                · rcases p6955_3 (m.d 1 3) (by simp) with h6961 | h6961
                  · linarith only [h6961, hlam, p6955_0]
                  · rcases p6955_3 (m.d 1 4) (by simp) with h6963 | h6963
                    · linarith only [h2, h6963, hlam]
                    · linarith only [h4129, h6963, hlam]
              · linarith only [h6958, hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              rcases p6955_3 (m.d 0 1) (by simp) with h6967 | h6967
              · rcases p6955_3 (m.d 1 2) (by simp) with h6968 | h6968
                · linarith only [h0, h6968, hlam]
                · rcases p6955_3 (m.d 1 3) (by simp) with h6970 | h6970
                  · linarith only [h1, h6970, hlam]
                  · rcases p6955_3 (m.d 1 4) (by simp) with h6972 | h6972
                    · linarith only [h6972, hlam, p6955_0]
                    · rcases p6955_3 (m.d 1 5) (by simp) with h6974 | h6974
                      · linarith only [h3, h6974, hlam]
                      · rcases h1emax with h6976 | h6976 | h6976 | h6976 | h6976
                        · linarith only [h0, h4, h4058, h6950, h6952, h6976, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h2bigk with h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c | h6978c
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h4, h4058, h6950, h6952, h7, hlam, p6978_2]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            rcases p6978_3 (m.d 0 2) (by simp) with h6981 | h6981
                            · rcases p6978_3 (m.d 1 2) (by simp) with h6982 | h6982
                              · linarith only [h0, h6982, hlam]
                              · rcases p6978_3 (m.d 2 3) (by simp) with h6984 | h6984
                                · linarith only [h6984, hlam, p6978_0]
                                · rcases p6978_3 (m.d 2 4) (by simp) with h6986 | h6986
                                  · linarith only [h5, h6986, hlam]
                                  · linarith only [h6950, h6986, hlam]
                            · linarith only [h6981, hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            rcases p6978_3 (m.d 0 2) (by simp) with h6990 | h6990
                            · rcases p6978_3 (m.d 1 2) (by simp) with h6991 | h6991
                              · linarith only [h0, h6991, hlam]
                              · rcases p6978_3 (m.d 2 3) (by simp) with h6993 | h6993
                                · linarith only [h4, h6993, hlam]
                                · rcases p6978_3 (m.d 2 4) (by simp) with h6995 | h6995
                                  · linarith only [h6995, hlam, p6978_0]
                                  · rcases p6978_3 (m.d 2 5) (by simp) with h6997 | h6997
                                    · linarith only [h6, h6997, hlam]
                                    · rcases h4bigk with h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c | h6999c
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        rcases p6999_3 (m.d 0 4) (by simp) with h7001 | h7001
                                        · rcases p6999_3 (m.d 1 4) (by simp) with h7002 | h7002
                                          · linarith only [h2, h7002, hlam]
                                          · rcases p6999_3 (m.d 2 4) (by simp) with h7004 | h7004
                                            · linarith only [h5, h7004, hlam]
                                            · linarith only [h3576, h7004, hlam]
                                        · linarith only [h2, h7001, hlam]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        rcases p6999_3 (m.d 0 4) (by simp) with h7008 | h7008
                                        · rcases p6999_3 (m.d 1 4) (by simp) with h7009 | h7009
                                          · linarith only [h2, h7009, hlam]
                                          · rcases p6999_3 (m.d 2 4) (by simp) with h7011 | h7011
                                            · linarith only [h5, h7011, hlam]
                                            · rcases p6999_3 (m.d 3 4) (by simp) with h7013 | h7013
                                              · linarith only [h7, h7013, hlam]
                                              · linarith only [h6950, h7013, hlam]
                                        · linarith only [h5, h7008, hlam]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h0, h4, h4058, h6950, h6952, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6999_1]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        rcases p6999_3 (m.d 0 4) (by simp) with h7018 | h7018
                                        · rcases p6999_3 (m.d 1 4) (by simp) with h7019 | h7019
                                          · linarith only [h2, h7019, hlam]
                                          · linarith only [h6949, h7019, hlam]
                                        · linarith only [h7018, hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h2, hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h3576, hlam, p6999_1]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h4129, hlam, p6999_1]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p6955_1, p6999_1]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h5, hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p6978_1, p6999_1]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h6950, hlam, p6999_1]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p6978_1, p6999_1]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h7, hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h0, h4, h4129, h6948, h6954, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p6999_1]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h4, h7, hlam, p6978_2, p6999_1]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        rcases p6999_3 (m.d 0 4) (by simp) with h7037 | h7037
                                        · rcases p6999_3 (m.d 1 4) (by simp) with h7038 | h7038
                                          · linarith only [h4129, h7038, hlam]
                                          · linarith only [h6949, h7038, hlam]
                                        · linarith only [h7037, h9, hlam]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h9, hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h6949, hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h6953, hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [h6954, hlam, p6999_0]
                                      · have p6999_0 := h6999c.1
                                        have p6999_1 := h6999c.2.1
                                        have p6999_2 := h6999c.2.2.1
                                        have p6999_3 := h6999c.2.2.2
                                        linarith only [hlam, p6999_0]
                            · linarith only [h6990, hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            rcases p6978_3 (m.d 0 2) (by simp) with h7048 | h7048
                            · rcases p6978_3 (m.d 1 2) (by simp) with h7049 | h7049
                              · linarith only [h0, h7049, hlam]
                              · rcases p6978_3 (m.d 2 3) (by simp) with h7051 | h7051
                                · linarith only [h4, h7051, hlam]
                                · linarith only [h6952, h7051, hlam]
                            · linarith only [h7048, hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h0, hlam, p6978_1]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h10, hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h3576, hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h4058, hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h4, hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h0, h4, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6978_1]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h6950, hlam, p6978_1]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h0, h4, h4058, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6978_1]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h5, hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            rcases p6978_3 (m.d 0 2) (by simp) with h7066 | h7066
                            · rcases p6978_3 (m.d 1 2) (by simp) with h7067 | h7067
                              · linarith only [h7067, hlam, p6978_0]
                              · rcases p6978_3 (m.d 2 3) (by simp) with h7069 | h7069
                                · linarith only [h6950, h7069, hlam]
                                · linarith only [h10, h7069, hlam]
                            · linarith only [h0, h7066, hlam]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6978_1]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h0, h4, h4058, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6978_1]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h6, hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h0, h4, h6950, h6952, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6978_1]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h6952, hlam, p6978_0]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [h6953, hlam, p6978_1]
                          · have p6978_0 := h6978c.1
                            have p6978_1 := h6978c.2.1
                            have p6978_2 := h6978c.2.2.1
                            have p6978_3 := h6978c.2.2.2
                            linarith only [hlam, p6978_0]
                        · rcases h2bigk with h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c | h7081c
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h10, h4, h6950, h7, hlam, p7081_2]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            rcases p7081_3 (m.d 0 2) (by simp) with h7084 | h7084
                            · rcases p7081_3 (m.d 1 2) (by simp) with h7085 | h7085
                              · linarith only [h0, h7085, hlam]
                              · rcases p7081_3 (m.d 2 3) (by simp) with h7087 | h7087
                                · linarith only [h7087, hlam, p7081_0]
                                · rcases p7081_3 (m.d 2 4) (by simp) with h7089 | h7089
                                  · linarith only [h5, h7089, hlam]
                                  · linarith only [h6950, h7089, hlam]
                            · linarith only [h7084, hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            rcases p7081_3 (m.d 0 2) (by simp) with h7093 | h7093
                            · rcases p7081_3 (m.d 1 2) (by simp) with h7094 | h7094
                              · linarith only [h0, h7094, hlam]
                              · rcases p7081_3 (m.d 2 3) (by simp) with h7096 | h7096
                                · linarith only [h4, h7096, hlam]
                                · rcases p7081_3 (m.d 2 4) (by simp) with h7098 | h7098
                                  · linarith only [h7098, hlam, p7081_0]
                                  · rcases p7081_3 (m.d 2 5) (by simp) with h7100 | h7100
                                    · linarith only [h6, h7100, hlam]
                                    · rcases h4bigk with h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        rcases p7102_3 (m.d 0 4) (by simp) with h7104 | h7104
                                        · rcases p7102_3 (m.d 1 4) (by simp) with h7105 | h7105
                                          · linarith only [h2, h7105, hlam]
                                          · rcases p7102_3 (m.d 2 4) (by simp) with h7107 | h7107
                                            · linarith only [h5, h7107, hlam]
                                            · linarith only [h3576, h7107, hlam]
                                        · linarith only [h2, h7104, hlam]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        rcases p7102_3 (m.d 0 4) (by simp) with h7111 | h7111
                                        · rcases p7102_3 (m.d 1 4) (by simp) with h7112 | h7112
                                          · linarith only [h2, h7112, hlam]
                                          · rcases p7102_3 (m.d 2 4) (by simp) with h7114 | h7114
                                            · linarith only [h5, h7114, hlam]
                                            · rcases p7102_3 (m.d 3 4) (by simp) with h7116 | h7116
                                              · linarith only [h7, h7116, hlam]
                                              · linarith only [h6950, h7116, hlam]
                                        · linarith only [h5, h7111, hlam]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h4129, h6948, h6954, hc04, hc45, hlam, hphi, ht0b, ht5b, p7102_1]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        rcases p7102_3 (m.d 0 4) (by simp) with h7121 | h7121
                                        · rcases p7102_3 (m.d 1 4) (by simp) with h7122 | h7122
                                          · linarith only [h2, h7122, hlam]
                                          · linarith only [h6949, h7122, hlam]
                                        · linarith only [h7121, hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h2, hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h3576, hlam, p7102_1]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h4129, hlam, p7102_1]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p6955_1, p7102_1]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h5, hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p7081_1, p7102_1]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h6950, hlam, p7102_1]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p7081_1, p7102_1]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h7, hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h0, h4, h4129, h6948, h6954, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p7102_1]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h4, h7, hlam, p7081_2, p7102_1]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        rcases p7102_3 (m.d 0 4) (by simp) with h7140 | h7140
                                        · rcases p7102_3 (m.d 1 4) (by simp) with h7141 | h7141
                                          · linarith only [h4129, h7141, hlam]
                                          · linarith only [h6949, h7141, hlam]
                                        · linarith only [h7140, h9, hlam]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h9, hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h6949, hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h6953, hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [h6954, hlam, p7102_0]
                                      · have p7102_0 := h7102c.1
                                        have p7102_1 := h7102c.2.1
                                        have p7102_2 := h7102c.2.2.1
                                        have p7102_3 := h7102c.2.2.2
                                        linarith only [hlam, p7102_0]
                            · linarith only [h7093, hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            rcases p7081_3 (m.d 0 2) (by simp) with h7151 | h7151
                            · rcases p7081_3 (m.d 1 2) (by simp) with h7152 | h7152
                              · linarith only [h0, h7152, hlam]
                              · rcases p7081_3 (m.d 2 3) (by simp) with h7154 | h7154
                                · linarith only [h4, h7154, hlam]
                                · linarith only [h6952, h7154, hlam]
                            · linarith only [h7151, hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h0, hlam, p7081_1]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h10, hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h3576, hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h4058, hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h4, hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h0, h4, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7081_1]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h6950, hlam, p7081_1]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h0, h4, h4058, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7081_1]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h5, hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            rcases p7081_3 (m.d 0 2) (by simp) with h7169 | h7169
                            · rcases p7081_3 (m.d 1 2) (by simp) with h7170 | h7170
                              · linarith only [h7170, hlam, p7081_0]
                              · rcases p7081_3 (m.d 2 3) (by simp) with h7172 | h7172
                                · linarith only [h6950, h7172, hlam]
                                · linarith only [h10, h7172, hlam]
                            · linarith only [h0, h7169, hlam]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7081_1]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h0, h4, h4058, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7081_1]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h6, hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h0, h4, h6950, h6952, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7081_1]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h6952, hlam, p7081_0]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [h6953, hlam, p7081_1]
                          · have p7081_0 := h7081c.1
                            have p7081_1 := h7081c.2.1
                            have p7081_2 := h7081c.2.2.1
                            have p7081_3 := h7081c.2.2.2
                            linarith only [hlam, p7081_0]
                        · rcases h2bigk with h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c | h7184c
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h10, h4, h6950, h7, hlam, p7184_2]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            rcases p7184_3 (m.d 0 2) (by simp) with h7187 | h7187
                            · rcases p7184_3 (m.d 1 2) (by simp) with h7188 | h7188
                              · linarith only [h0, h7188, hlam]
                              · rcases p7184_3 (m.d 2 3) (by simp) with h7190 | h7190
                                · linarith only [h7190, hlam, p7184_0]
                                · rcases p7184_3 (m.d 2 4) (by simp) with h7192 | h7192
                                  · linarith only [h5, h7192, hlam]
                                  · linarith only [h6950, h7192, hlam]
                            · linarith only [h7187, hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            rcases p7184_3 (m.d 0 2) (by simp) with h7196 | h7196
                            · rcases p7184_3 (m.d 1 2) (by simp) with h7197 | h7197
                              · linarith only [h0, h7197, hlam]
                              · rcases p7184_3 (m.d 2 3) (by simp) with h7199 | h7199
                                · linarith only [h4, h7199, hlam]
                                · rcases p7184_3 (m.d 2 4) (by simp) with h7201 | h7201
                                  · linarith only [h7201, hlam, p7184_0]
                                  · rcases p7184_3 (m.d 2 5) (by simp) with h7203 | h7203
                                    · linarith only [h6, h7203, hlam]
                                    · rcases h4bigk with h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c | h7205c
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        rcases p7205_3 (m.d 0 4) (by simp) with h7207 | h7207
                                        · rcases p7205_3 (m.d 1 4) (by simp) with h7208 | h7208
                                          · linarith only [h2, h7208, hlam]
                                          · rcases p7205_3 (m.d 2 4) (by simp) with h7210 | h7210
                                            · linarith only [h5, h7210, hlam]
                                            · linarith only [h3576, h7210, hlam]
                                        · linarith only [h2, h7207, hlam]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        rcases p7205_3 (m.d 0 4) (by simp) with h7214 | h7214
                                        · rcases p7205_3 (m.d 1 4) (by simp) with h7215 | h7215
                                          · linarith only [h2, h7215, hlam]
                                          · rcases p7205_3 (m.d 2 4) (by simp) with h7217 | h7217
                                            · linarith only [h5, h7217, hlam]
                                            · rcases p7205_3 (m.d 3 4) (by simp) with h7219 | h7219
                                              · linarith only [h7, h7219, hlam]
                                              · linarith only [h6950, h7219, hlam]
                                        · linarith only [h5, h7214, hlam]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h4129, h6948, h6954, hc04, hc45, hlam, hphi, ht0b, ht5b, p7205_1]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        rcases p7205_3 (m.d 0 4) (by simp) with h7224 | h7224
                                        · rcases p7205_3 (m.d 1 4) (by simp) with h7225 | h7225
                                          · linarith only [h2, h7225, hlam]
                                          · linarith only [h6949, h7225, hlam]
                                        · linarith only [h7224, hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h2, hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h3576, hlam, p7205_1]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h4129, hlam, p7205_1]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p6955_1, p7205_1]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h5, hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p7184_1, p7205_1]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h6950, hlam, p7205_1]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p7184_1, p7205_1]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h7, hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h0, h4, h4129, h6948, h6954, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p7205_1]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h4, h7, hlam, p7184_2, p7205_1]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        rcases p7205_3 (m.d 0 4) (by simp) with h7243 | h7243
                                        · rcases p7205_3 (m.d 1 4) (by simp) with h7244 | h7244
                                          · linarith only [h4129, h7244, hlam]
                                          · linarith only [h6949, h7244, hlam]
                                        · linarith only [h7243, h9, hlam]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h9, hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h6949, hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h6953, hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [h6954, hlam, p7205_0]
                                      · have p7205_0 := h7205c.1
                                        have p7205_1 := h7205c.2.1
                                        have p7205_2 := h7205c.2.2.1
                                        have p7205_3 := h7205c.2.2.2
                                        linarith only [hlam, p7205_0]
                            · linarith only [h7196, hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            rcases p7184_3 (m.d 0 2) (by simp) with h7254 | h7254
                            · rcases p7184_3 (m.d 1 2) (by simp) with h7255 | h7255
                              · linarith only [h0, h7255, hlam]
                              · rcases p7184_3 (m.d 2 3) (by simp) with h7257 | h7257
                                · linarith only [h4, h7257, hlam]
                                · linarith only [h6952, h7257, hlam]
                            · linarith only [h7254, hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h0, hlam, p7184_1]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h10, hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h3576, hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h4058, hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h4, hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h0, h4, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7184_1]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h6950, hlam, p7184_1]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h0, h4, h4058, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7184_1]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h5, hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            rcases p7184_3 (m.d 0 2) (by simp) with h7272 | h7272
                            · rcases p7184_3 (m.d 1 2) (by simp) with h7273 | h7273
                              · linarith only [h7273, hlam, p7184_0]
                              · rcases p7184_3 (m.d 2 3) (by simp) with h7275 | h7275
                                · linarith only [h6950, h7275, hlam]
                                · linarith only [h10, h7275, hlam]
                            · linarith only [h0, h7272, hlam]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h10, hc12, hc24, hlam, hphi, p7184_1]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h0, h4, h4058, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7184_1]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h6, hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h0, h4, h6950, h6952, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7184_1]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h6952, hlam, p7184_0]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [h6953, hlam, p7184_1]
                          · have p7184_0 := h7184c.1
                            have p7184_1 := h7184c.2.1
                            have p7184_2 := h7184c.2.2.1
                            have p7184_3 := h7184c.2.2.2
                            linarith only [hlam, p7184_0]
                        · rcases h2bigk with h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c | h7287c
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h10, h4, h6950, h7, hlam, p7287_2]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            rcases p7287_3 (m.d 0 2) (by simp) with h7290 | h7290
                            · rcases p7287_3 (m.d 1 2) (by simp) with h7291 | h7291
                              · linarith only [h0, h7291, hlam]
                              · rcases p7287_3 (m.d 2 3) (by simp) with h7293 | h7293
                                · linarith only [h7293, hlam, p7287_0]
                                · rcases p7287_3 (m.d 2 4) (by simp) with h7295 | h7295
                                  · linarith only [h5, h7295, hlam]
                                  · linarith only [h6950, h7295, hlam]
                            · linarith only [h7290, hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            rcases p7287_3 (m.d 0 2) (by simp) with h7299 | h7299
                            · rcases p7287_3 (m.d 1 2) (by simp) with h7300 | h7300
                              · linarith only [h0, h7300, hlam]
                              · rcases p7287_3 (m.d 2 3) (by simp) with h7302 | h7302
                                · linarith only [h4, h7302, hlam]
                                · rcases p7287_3 (m.d 2 4) (by simp) with h7304 | h7304
                                  · linarith only [h7304, hlam, p7287_0]
                                  · rcases p7287_3 (m.d 2 5) (by simp) with h7306 | h7306
                                    · linarith only [h6, h7306, hlam]
                                    · rcases h4bigk with h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c | h7308c
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        rcases p7308_3 (m.d 0 4) (by simp) with h7310 | h7310
                                        · rcases p7308_3 (m.d 1 4) (by simp) with h7311 | h7311
                                          · linarith only [h2, h7311, hlam]
                                          · rcases p7308_3 (m.d 2 4) (by simp) with h7313 | h7313
                                            · linarith only [h5, h7313, hlam]
                                            · linarith only [h3576, h7313, hlam]
                                        · linarith only [h2, h7310, hlam]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        rcases p7308_3 (m.d 0 4) (by simp) with h7317 | h7317
                                        · rcases p7308_3 (m.d 1 4) (by simp) with h7318 | h7318
                                          · linarith only [h2, h7318, hlam]
                                          · rcases p7308_3 (m.d 2 4) (by simp) with h7320 | h7320
                                            · linarith only [h5, h7320, hlam]
                                            · rcases p7308_3 (m.d 3 4) (by simp) with h7322 | h7322
                                              · linarith only [h7, h7322, hlam]
                                              · linarith only [h6950, h7322, hlam]
                                        · linarith only [h5, h7317, hlam]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h4129, h6948, h6954, hc04, hc45, hlam, hphi, ht0b, ht5b, p7308_1]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        rcases p7308_3 (m.d 0 4) (by simp) with h7327 | h7327
                                        · rcases p7308_3 (m.d 1 4) (by simp) with h7328 | h7328
                                          · linarith only [h2, h7328, hlam]
                                          · linarith only [h6949, h7328, hlam]
                                        · linarith only [h7327, hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h2, hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h3576, hlam, p7308_1]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h4129, hlam, p7308_1]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p6955_1, p7308_1]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h5, hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h0, hlam, p6955_2, p7287_1, p7308_1]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h6950, hlam, p7308_1]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p7287_1, p7308_1]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h7, hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h0, h4, h4129, h6948, h6954, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p7308_1]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h4, h7, hlam, p7287_2, p7308_1]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        rcases p7308_3 (m.d 0 4) (by simp) with h7346 | h7346
                                        · rcases p7308_3 (m.d 1 4) (by simp) with h7347 | h7347
                                          · linarith only [h4129, h7347, hlam]
                                          · linarith only [h6949, h7347, hlam]
                                        · linarith only [h7346, h9, hlam]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h9, hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h6949, hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h6953, hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [h6954, hlam, p7308_0]
                                      · have p7308_0 := h7308c.1
                                        have p7308_1 := h7308c.2.1
                                        have p7308_2 := h7308c.2.2.1
                                        have p7308_3 := h7308c.2.2.2
                                        linarith only [hlam, p7308_0]
                            · linarith only [h7299, hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            rcases p7287_3 (m.d 0 2) (by simp) with h7357 | h7357
                            · rcases p7287_3 (m.d 1 2) (by simp) with h7358 | h7358
                              · linarith only [h0, h7358, hlam]
                              · rcases p7287_3 (m.d 2 3) (by simp) with h7360 | h7360
                                · linarith only [h4, h7360, hlam]
                                · linarith only [h6952, h7360, hlam]
                            · linarith only [h7357, hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h0, hlam, p7287_1]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h10, hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h3576, hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h4058, hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h4, hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h0, h4, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7287_1]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h6950, hlam, p7287_1]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h0, h4, h4058, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7287_1]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h5, hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            rcases p7287_3 (m.d 0 2) (by simp) with h7375 | h7375
                            · rcases p7287_3 (m.d 1 2) (by simp) with h7376 | h7376
                              · linarith only [h7376, hlam, p7287_0]
                              · rcases p7287_3 (m.d 2 3) (by simp) with h7378 | h7378
                                · linarith only [h6950, h7378, hlam]
                                · linarith only [h10, h7378, hlam]
                            · linarith only [h0, h7375, hlam]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h10, hc12, hc24, hlam, hphi, p7287_1]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h0, h4, h4058, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7287_1]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h6, hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h0, h4, h6950, h6952, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7287_1]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h6952, hlam, p7287_0]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [h6953, hlam, p7287_1]
                          · have p7287_0 := h7287c.1
                            have p7287_1 := h7287c.2.1
                            have p7287_2 := h7287c.2.2.1
                            have p7287_3 := h7287c.2.2.2
                            linarith only [hlam, p7287_0]
              · linarith only [h6967, hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              rcases p6955_3 (m.d 0 1) (by simp) with h7391 | h7391
              · rcases p6955_3 (m.d 1 2) (by simp) with h7392 | h7392
                · linarith only [h0, h7392, hlam]
                · rcases p6955_3 (m.d 1 3) (by simp) with h7394 | h7394
                  · linarith only [h1, h7394, hlam]
                  · linarith only [h6948, h7394, hlam]
              · linarith only [h7391, hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h0, hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h10, hlam, p6955_1]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h3576, hlam, p6955_1]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h4058, hlam, p6955_1]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h1, hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h0, h10, h4, h6950, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6955_1]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h4129, hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h0, h10, h4, h6950, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p6955_1]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h2, hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              rcases p6955_3 (m.d 0 1) (by simp) with h7409 | h7409
              · rcases p6955_3 (m.d 1 2) (by simp) with h7410 | h7410
                · linarith only [h3576, h7410, hlam]
                · rcases p6955_3 (m.d 1 3) (by simp) with h7412 | h7412
                  · linarith only [h4129, h7412, hlam]
                  · linarith only [h10, h7412, hlam]
              · linarith only [h0, h7409, hlam]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h2, h6948, h6954, hc01, hc45, hlam, hphi, ht0b, ht5b, p6955_1]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              rcases p6955_3 (m.d 0 1) (by simp) with h7418 | h7418
              · rcases p6955_3 (m.d 1 2) (by simp) with h7419 | h7419
                · linarith only [h3576, h7419, hlam]
                · rcases p6955_3 (m.d 1 3) (by simp) with h7421 | h7421
                  · linarith only [h4129, h7421, hlam]
                  · linarith only [h6948, h7421, hlam]
              · linarith only [h3, h7418, hlam]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h3, hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h0, h4, h4058, h6950, h6952, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6955_1]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h6948, hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [h6949, hlam, p6955_0]
            · have p6955_0 := h6955c.1
              have p6955_1 := h6955c.2.1
              have p6955_2 := h6955c.2.2.1
              have p6955_3 := h6955c.2.2.2
              linarith only [hlam, p6955_0]
          · linarith only [h10, h6950, h6954, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h3576, h6949, h6953, hlam]
      · linarith only [h10, h6948, h6952, hlam]
  · linarith only [h4129, h6948, h6949, hlam]

end R2N4
