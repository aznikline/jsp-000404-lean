import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5090000 in
set_option maxHeartbeats 5090000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg3476 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg4023 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4106 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4107 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4108 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h3476 := hg3476
  have h4023 := hg4023
  rcases m.htr 1 2 3 (by decide) (by decide) with h4946 | h4946
  · linarith only [h0, h4, h4107, h4946, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4948 | h4948
    · linarith only [h0, h3476, h4948, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4950 | h4950
      · linarith only [h0, h4023, h4950, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4952 | h4952
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4953 | h4953
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4954 | h4954
            · linarith only [h2, h4108, h4954, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4956 | h4956
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4957 | h4957
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4958 | h4958
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4959 | h4959
                    · linarith only [h3476, h4, h4106, h4108, h4959, hc02, hc23, hlam, hphi]
                    · rcases h0bigk with h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c | h4961c
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        rcases p4961_3 (m.d 0 1) (by simp) with h4963 | h4963
                        · rcases p4961_3 (m.d 0 2) (by simp) with h4964 | h4964
                          · linarith only [h0, h4964, hlam]
                          · rcases p4961_3 (m.d 0 3) (by simp) with h4966 | h4966
                            · linarith only [h1, h4966, hlam]
                            · linarith only [h4, h4966, hlam]
                        · linarith only [h0, h4963, hlam]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h1, h4953, hc01, hlam, hphi, ht0b, ht5b, p4961_1, u5ehi3]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        rcases p4961_3 (m.d 0 1) (by simp) with h4971 | h4971
                        · rcases p4961_3 (m.d 0 2) (by simp) with h4972 | h4972
                          · linarith only [h0, h4972, hlam]
                          · rcases p4961_3 (m.d 0 3) (by simp) with h4974 | h4974
                            · linarith only [h1, h4974, hlam]
                            · linarith only [h4106, h4974, hlam]
                        · linarith only [h2, h4971, hlam]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        rcases p4961_3 (m.d 0 1) (by simp) with h4978 | h4978
                        · rcases p4961_3 (m.d 0 2) (by simp) with h4979 | h4979
                          · linarith only [h0, h4979, hlam]
                          · rcases p4961_3 (m.d 0 3) (by simp) with h4981 | h4981
                            · linarith only [h1, h4981, hlam]
                            · linarith only [h4107, h4981, hlam]
                        · linarith only [h3, h4978, hlam]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h0, hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h4, hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h3476, hlam, p4961_1]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h4023, hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h1, hlam, p4961_1]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        rcases p4961_3 (m.d 0 1) (by simp) with h4991 | h4991
                        · rcases p4961_3 (m.d 0 2) (by simp) with h4992 | h4992
                          · linarith only [h4, h4992, hlam]
                          · rcases p4961_3 (m.d 0 3) (by simp) with h4994 | h4994
                            · rcases p4961_3 (m.d 0 4) (by simp) with h4995 | h4995
                              · linarith only [h4106, h4995, hlam]
                              · linarith only [h3476, h4995, hlam]
                            · linarith only [h4, h4994, hlam]
                        · linarith only [h0, h4991, hlam]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        rcases p4961_3 (m.d 0 1) (by simp) with h5001 | h5001
                        · rcases p4961_3 (m.d 0 2) (by simp) with h5002 | h5002
                          · linarith only [h4, h5002, hlam]
                          · rcases p4961_3 (m.d 0 3) (by simp) with h5004 | h5004
                            · rcases p4961_3 (m.d 0 4) (by simp) with h5005 | h5005
                              · linarith only [h4106, h5005, hlam]
                              · rcases p4961_3 (m.d 0 5) (by simp) with h5007 | h5007
                                · linarith only [h4107, h5007, hlam]
                                · linarith only [h4108, h5007, hlam]
                            · linarith only [h4106, h5004, hlam]
                        · linarith only [h2, h5001, hlam]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        rcases p4961_3 (m.d 0 1) (by simp) with h5012 | h5012
                        · rcases p4961_3 (m.d 0 2) (by simp) with h5013 | h5013
                          · linarith only [h4, h5013, hlam]
                          · rcases p4961_3 (m.d 0 3) (by simp) with h5015 | h5015
                            · rcases p4961_3 (m.d 0 4) (by simp) with h5016 | h5016
                              · linarith only [h4106, h5016, hlam]
                              · rcases p4961_3 (m.d 0 5) (by simp) with h5018 | h5018
                                · linarith only [h4107, h5018, hlam]
                                · rcases h2bigk with h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h3476, h4108, h4958, hc12, hc24, hlam, hphi, p5020_1]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h4, hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h3476, hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h4023, hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h0, hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h4946, hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h4948, hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h4950, hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    rcases p5020_3 (m.d 0 2) (by simp) with h5031 | h5031
                                    · linarith only [h5031, hlam, p5020_0]
                                    · rcases p5020_3 (m.d 1 2) (by simp) with h5033 | h5033
                                      · linarith only [h4946, h5033, hlam]
                                      · rcases p5020_3 (m.d 2 3) (by simp) with h5035 | h5035
                                        · rcases p5020_3 (m.d 2 4) (by simp) with h5036 | h5036
                                          · linarith only [h4956, h5036, hlam]
                                          · linarith only [h3476, h5036, hlam]
                                        · linarith only [h5035, hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    rcases p5020_3 (m.d 0 2) (by simp) with h5040 | h5040
                                    · linarith only [h4, h5040, hlam]
                                    · linarith only [h0, h5040, hlam]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h4958, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5020_1, u5ehi4]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h4023, hc02, hc23, hlam, hphi, p5020_1]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    rcases p5020_3 (m.d 0 2) (by simp) with h5046 | h5046
                                    · linarith only [h5046, hlam, p5020_0]
                                    · rcases p5020_3 (m.d 1 2) (by simp) with h5048 | h5048
                                      · linarith only [h4948, h5048, hlam]
                                      · rcases p5020_3 (m.d 2 3) (by simp) with h5050 | h5050
                                        · rcases p5020_3 (m.d 2 4) (by simp) with h5051 | h5051
                                          · rcases p5020_3 (m.d 2 5) (by simp) with h5052 | h5052
                                            · linarith only [h4958, h5052, hlam]
                                            · linarith only [h4023, h5052, hlam]
                                          · linarith only [h5051, hlam, p5020_0]
                                        · linarith only [h4, h5050, hlam]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    rcases p5020_3 (m.d 0 2) (by simp) with h5057 | h5057
                                    · linarith only [h3476, h5057, hlam]
                                    · linarith only [h0, h5057, hlam]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h4956, hlam, p5020_1]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h0, h3476, h4108, h4958, hc12, hc24, hlam, hphi, p5020_1]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    rcases p5020_3 (m.d 0 2) (by simp) with h5063 | h5063
                                    · linarith only [h5063, hlam, p5020_0]
                                    · rcases p5020_3 (m.d 1 2) (by simp) with h5065 | h5065
                                      · linarith only [h4950, h5065, hlam]
                                      · rcases p5020_3 (m.d 2 3) (by simp) with h5067 | h5067
                                        · rcases p5020_3 (m.d 2 4) (by simp) with h5068 | h5068
                                          · rcases p5020_3 (m.d 2 5) (by simp) with h5069 | h5069
                                            · rcases h3bigk with h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c | h5070c
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4, h4953, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5070_1, u5ehi3]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4, hlam, p5070_1]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                rcases p5070_3 (m.d 0 3) (by simp) with h5074 | h5074
                                                · rcases p5070_3 (m.d 1 3) (by simp) with h5075 | h5075
                                                  · linarith only [h1, h5075, hlam]
                                                  · linarith only [h4952, h5075, hlam]
                                                · linarith only [h5074, hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                rcases p5070_3 (m.d 0 3) (by simp) with h5079 | h5079
                                                · rcases p5070_3 (m.d 1 3) (by simp) with h5080 | h5080
                                                  · linarith only [h1, h5080, hlam]
                                                  · linarith only [h4953, h5080, hlam]
                                                · linarith only [h5079, hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h1, hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4946, hlam, p5070_1]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                rcases p5070_3 (m.d 0 3) (by simp) with h5087 | h5087
                                                · rcases p5070_3 (m.d 1 3) (by simp) with h5088 | h5088
                                                  · rcases p5070_3 (m.d 2 3) (by simp) with h5089 | h5089
                                                    · rcases p5070_3 (m.d 3 4) (by simp) with h5090 | h5090
                                                      · linarith only [h5090, hlam, p5070_0]
                                                      · rcases p5070_3 (m.d 3 5) (by simp) with h5092 | h5092
                                                        · linarith only [h4953, h5092, hlam]
                                                        · linarith only [h4959, h5092, hlam]
                                                    · linarith only [h4956, h5089, hlam]
                                                  · linarith only [h5088, hlam, p5070_0]
                                                · linarith only [h4106, h5087, hlam]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p5070_1, u5ehi3]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4961_1, p5070_1, u5ehi0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4953, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5070_1, u5ehi3]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                rcases p5070_3 (m.d 0 3) (by simp) with h5102 | h5102
                                                · linarith only [h4, h5102, hlam]
                                                · linarith only [h4106, h5102, hlam]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                rcases p5070_3 (m.d 0 3) (by simp) with h5105 | h5105
                                                · linarith only [h4, h5105, hlam]
                                                · linarith only [h4107, h5105, hlam]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4106, hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4952, hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4956, hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4959, hlam, p5070_1]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4107, hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4953, hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h4957, hlam, p5070_0]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [h3, h4953, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4961_1, p5070_1]
                                              · have p5070_0 := h5070c.1
                                                have p5070_1 := h5070c.2.1
                                                have p5070_2 := h5070c.2.2.1
                                                have p5070_3 := h5070c.2.2.2
                                                linarith only [hlam, p5070_0]
                                            · linarith only [h5069, hlam, p5020_0]
                                          · linarith only [h3476, h5068, hlam]
                                        · linarith only [h4, h5067, hlam]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    rcases p5020_3 (m.d 0 2) (by simp) with h5121 | h5121
                                    · linarith only [h4023, h5121, hlam]
                                    · linarith only [h0, h5121, hlam]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h4957, hlam, p5020_1]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [h4958, hlam, p5020_0]
                                  · have p5020_0 := h5020c.1
                                    have p5020_1 := h5020c.2.1
                                    have p5020_2 := h5020c.2.2.1
                                    have p5020_3 := h5020c.2.2.2
                                    linarith only [hlam, p5020_0]
                            · linarith only [h4107, h5015, hlam]
                        · linarith only [h3, h5012, hlam]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h2, hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h0, h4108, hc12, hc45, hlam, hphi, ht23, ht34, p4961_1]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h4106, hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h4108, hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h3, hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h0, h4108, h4956, h4958, hc12, hc23, hlam, hphi, p4961_1]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h4107, hlam, p4961_0]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [h0, h3476, h4108, h4956, h4958, hc12, hc23, hlam, hphi, p4961_1]
                      · have p4961_0 := h4961c.1
                        have p4961_1 := h4961c.2.1
                        have p4961_2 := h4961c.2.2.1
                        have p4961_3 := h4961c.2.2.2
                        linarith only [hlam, p4961_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5139 | h5139
                    · linarith only [h0, h3476, h4958, h5139, hc12, hc34, hlam, hphi, ht23]
                    · rcases h0bigk with h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c | h5141c
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        rcases p5141_3 (m.d 0 1) (by simp) with h5143 | h5143
                        · rcases p5141_3 (m.d 0 2) (by simp) with h5144 | h5144
                          · linarith only [h0, h5144, hlam]
                          · rcases p5141_3 (m.d 0 3) (by simp) with h5146 | h5146
                            · linarith only [h1, h5146, hlam]
                            · linarith only [h4, h5146, hlam]
                        · linarith only [h0, h5143, hlam]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h1, h4953, hc01, hlam, hphi, ht0b, ht5b, p5141_1, u5ehi3]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        rcases p5141_3 (m.d 0 1) (by simp) with h5151 | h5151
                        · rcases p5141_3 (m.d 0 2) (by simp) with h5152 | h5152
                          · linarith only [h0, h5152, hlam]
                          · rcases p5141_3 (m.d 0 3) (by simp) with h5154 | h5154
                            · linarith only [h1, h5154, hlam]
                            · linarith only [h4106, h5154, hlam]
                        · linarith only [h2, h5151, hlam]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        rcases p5141_3 (m.d 0 1) (by simp) with h5158 | h5158
                        · rcases p5141_3 (m.d 0 2) (by simp) with h5159 | h5159
                          · linarith only [h0, h5159, hlam]
                          · rcases p5141_3 (m.d 0 3) (by simp) with h5161 | h5161
                            · linarith only [h1, h5161, hlam]
                            · linarith only [h4107, h5161, hlam]
                        · linarith only [h3, h5158, hlam]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h0, hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h4, hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h3476, hlam, p5141_1]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h4023, hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h1, hlam, p5141_1]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        rcases p5141_3 (m.d 0 1) (by simp) with h5171 | h5171
                        · rcases p5141_3 (m.d 0 2) (by simp) with h5172 | h5172
                          · linarith only [h4, h5172, hlam]
                          · rcases p5141_3 (m.d 0 3) (by simp) with h5174 | h5174
                            · rcases p5141_3 (m.d 0 4) (by simp) with h5175 | h5175
                              · linarith only [h4106, h5175, hlam]
                              · linarith only [h3476, h5175, hlam]
                            · linarith only [h4, h5174, hlam]
                        · linarith only [h0, h5171, hlam]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        rcases p5141_3 (m.d 0 1) (by simp) with h5181 | h5181
                        · rcases p5141_3 (m.d 0 2) (by simp) with h5182 | h5182
                          · linarith only [h4, h5182, hlam]
                          · rcases p5141_3 (m.d 0 3) (by simp) with h5184 | h5184
                            · rcases p5141_3 (m.d 0 4) (by simp) with h5185 | h5185
                              · linarith only [h4106, h5185, hlam]
                              · rcases p5141_3 (m.d 0 5) (by simp) with h5187 | h5187
                                · linarith only [h4107, h5187, hlam]
                                · linarith only [h4108, h5187, hlam]
                            · linarith only [h4106, h5184, hlam]
                        · linarith only [h2, h5181, hlam]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        rcases p5141_3 (m.d 0 1) (by simp) with h5192 | h5192
                        · rcases p5141_3 (m.d 0 2) (by simp) with h5193 | h5193
                          · linarith only [h4, h5193, hlam]
                          · rcases p5141_3 (m.d 0 3) (by simp) with h5195 | h5195
                            · rcases p5141_3 (m.d 0 4) (by simp) with h5196 | h5196
                              · linarith only [h4106, h5196, hlam]
                              · rcases p5141_3 (m.d 0 5) (by simp) with h5198 | h5198
                                · linarith only [h4107, h5198, hlam]
                                · rcases h2bigk with h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c | h5200c
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h3476, hc12, hc24, hlam, hphi, p5200_1]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h4, hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h3476, hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h4023, hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h0, hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h4946, hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h4948, hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h4950, hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    rcases p5200_3 (m.d 0 2) (by simp) with h5211 | h5211
                                    · linarith only [h5211, hlam, p5200_0]
                                    · rcases p5200_3 (m.d 1 2) (by simp) with h5213 | h5213
                                      · linarith only [h4946, h5213, hlam]
                                      · rcases p5200_3 (m.d 2 3) (by simp) with h5215 | h5215
                                        · rcases p5200_3 (m.d 2 4) (by simp) with h5216 | h5216
                                          · linarith only [h4956, h5216, hlam]
                                          · linarith only [h3476, h5216, hlam]
                                        · linarith only [h5215, hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    rcases p5200_3 (m.d 0 2) (by simp) with h5220 | h5220
                                    · linarith only [h4, h5220, hlam]
                                    · linarith only [h0, h5220, hlam]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h3476, hc02, hc23, hlam, hphi, p5200_1]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h0, h4023, hc12, hc23, hlam, hphi, p5200_1]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h0, h4958, hc12, hc45, hlam, hphi, ht23, ht34, p5200_1]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h4958, hc12, hc45, hlam, hphi, ht23, ht34, p5200_1]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h4956, hlam, p5200_1]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [hlam, p5200_0]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h4958, hlam, p5200_1]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    rcases p5200_3 (m.d 0 2) (by simp) with h5231 | h5231
                                    · linarith only [h5231, hlam, p5200_0]
                                    · rcases p5200_3 (m.d 1 2) (by simp) with h5233 | h5233
                                      · linarith only [h4950, h5233, hlam]
                                      · rcases p5200_3 (m.d 2 3) (by simp) with h5235 | h5235
                                        · rcases p5200_3 (m.d 2 4) (by simp) with h5236 | h5236
                                          · linarith only [h4958, h5236, hlam]
                                          · linarith only [h3476, h5236, hlam]
                                        · linarith only [h4, h5235, hlam]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    rcases p5200_3 (m.d 0 2) (by simp) with h5240 | h5240
                                    · linarith only [h4023, h5240, hlam]
                                    · linarith only [h0, h5240, hlam]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h4957, hlam, p5200_1]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [h0, h3476, hc12, hc25, hlam, hphi, p5200_1]
                                  · have p5200_0 := h5200c.1
                                    have p5200_1 := h5200c.2.1
                                    have p5200_2 := h5200c.2.2.1
                                    have p5200_3 := h5200c.2.2.2
                                    linarith only [hlam, p5200_0]
                            · linarith only [h4107, h5195, hlam]
                        · linarith only [h3, h5192, hlam]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h2, hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h0, h4108, hc12, hc45, hlam, hphi, ht23, ht34, p5141_1]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h4106, hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h4108, hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h3, hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        rcases p5141_3 (m.d 0 1) (by simp) with h5254 | h5254
                        · rcases p5141_3 (m.d 0 2) (by simp) with h5255 | h5255
                          · linarith only [h4023, h5255, hlam]
                          · rcases p5141_3 (m.d 0 3) (by simp) with h5257 | h5257
                            · rcases p5141_3 (m.d 0 4) (by simp) with h5258 | h5258
                              · linarith only [h4108, h5258, hlam]
                              · linarith only [h3476, h5258, hlam]
                            · linarith only [h4, h5257, hlam]
                        · linarith only [h0, h5254, hlam]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [h4107, hlam, p5141_0]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        rcases p5141_3 (m.d 0 1) (by simp) with h5264 | h5264
                        · rcases p5141_3 (m.d 0 2) (by simp) with h5265 | h5265
                          · linarith only [h4023, h5265, hlam]
                          · rcases p5141_3 (m.d 0 3) (by simp) with h5267 | h5267
                            · rcases p5141_3 (m.d 0 4) (by simp) with h5268 | h5268
                              · linarith only [h4108, h5268, hlam]
                              · rcases p5141_3 (m.d 0 5) (by simp) with h5270 | h5270
                                · rcases h2bigk with h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c | h5271c
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p5271_1]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4, hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h3476, hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4023, hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h0, hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4946, hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4948, hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4950, hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    rcases p5271_3 (m.d 0 2) (by simp) with h5282 | h5282
                                    · linarith only [h5282, hlam, p5271_0]
                                    · rcases p5271_3 (m.d 1 2) (by simp) with h5284 | h5284
                                      · linarith only [h4946, h5284, hlam]
                                      · rcases p5271_3 (m.d 2 3) (by simp) with h5286 | h5286
                                        · rcases p5271_3 (m.d 2 4) (by simp) with h5287 | h5287
                                          · linarith only [h4956, h5287, hlam]
                                          · linarith only [h3476, h5287, hlam]
                                        · linarith only [h5286, hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    rcases p5271_3 (m.d 0 2) (by simp) with h5291 | h5291
                                    · linarith only [h4, h5291, hlam]
                                    · linarith only [h0, h5291, hlam]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h3476, hc02, hc23, hlam, hphi, p5271_1]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4023, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5141_1, p5271_1]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h0, h4958, hc12, hc45, hlam, hphi, ht23, ht34, p5271_1]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4958, hc12, hc45, hlam, hphi, ht23, ht34, p5271_1]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4956, hlam, p5271_1]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [hlam, p5271_0]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4958, hlam, p5271_1]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    rcases p5271_3 (m.d 0 2) (by simp) with h5302 | h5302
                                    · linarith only [h5302, hlam, p5271_0]
                                    · rcases p5271_3 (m.d 1 2) (by simp) with h5304 | h5304
                                      · linarith only [h4950, h5304, hlam]
                                      · rcases p5271_3 (m.d 2 3) (by simp) with h5306 | h5306
                                        · rcases p5271_3 (m.d 2 4) (by simp) with h5307 | h5307
                                          · linarith only [h4958, h5307, hlam]
                                          · linarith only [h3476, h5307, hlam]
                                        · linarith only [h4, h5306, hlam]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    rcases p5271_3 (m.d 0 2) (by simp) with h5311 | h5311
                                    · linarith only [h4023, h5311, hlam]
                                    · linarith only [h0, h5311, hlam]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h4957, hlam, p5271_1]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [h0, h3476, hc12, hc25, hlam, hphi, p5271_1]
                                  · have p5271_0 := h5271c.1
                                    have p5271_1 := h5271c.2.1
                                    have p5271_2 := h5271c.2.2.1
                                    have p5271_3 := h5271c.2.2.2
                                    linarith only [hlam, p5271_0]
                                · linarith only [h4108, h5270, hlam]
                            · linarith only [h4106, h5267, hlam]
                        · linarith only [h2, h5264, hlam]
                      · have p5141_0 := h5141c.1
                        have p5141_1 := h5141c.2.1
                        have p5141_2 := h5141c.2.2.1
                        have p5141_3 := h5141c.2.2.2
                        linarith only [hlam, p5141_0]
                · linarith only [h1, h4, h4953, h4957, hlam]
              · linarith only [h1, h2, h4, h4952, h4953, h4956, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5323 | h5323
            · linarith only [h3476, h4107, h4108, h4952, h4953, h5323, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5325 | h5325
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5326 | h5326
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5327 | h5327
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5328 | h5328
                    · linarith only [h4107, h4108, h4952, h4953, h5328, hlam]
                    · rcases h0bigk with h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c | h5330c
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        rcases p5330_3 (m.d 0 1) (by simp) with h5332 | h5332
                        · rcases p5330_3 (m.d 0 2) (by simp) with h5333 | h5333
                          · linarith only [h0, h5333, hlam]
                          · rcases p5330_3 (m.d 0 3) (by simp) with h5335 | h5335
                            · linarith only [h1, h5335, hlam]
                            · linarith only [h4, h5335, hlam]
                        · linarith only [h0, h5332, hlam]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h4107, h4953, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5330_1]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        rcases p5330_3 (m.d 0 1) (by simp) with h5340 | h5340
                        · rcases p5330_3 (m.d 0 2) (by simp) with h5341 | h5341
                          · linarith only [h0, h5341, hlam]
                          · rcases p5330_3 (m.d 0 3) (by simp) with h5343 | h5343
                            · linarith only [h1, h5343, hlam]
                            · linarith only [h4106, h5343, hlam]
                        · linarith only [h2, h5340, hlam]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h4107, h4952, h4953, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5330_1]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h0, hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h4, hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h3476, hlam, p5330_1]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h4023, hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h1, hlam, p5330_1]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        rcases p5330_3 (m.d 0 1) (by simp) with h5354 | h5354
                        · rcases p5330_3 (m.d 0 2) (by simp) with h5355 | h5355
                          · linarith only [h4, h5355, hlam]
                          · rcases p5330_3 (m.d 0 3) (by simp) with h5357 | h5357
                            · rcases p5330_3 (m.d 0 4) (by simp) with h5358 | h5358
                              · linarith only [h4106, h5358, hlam]
                              · linarith only [h3476, h5358, hlam]
                            · linarith only [h4, h5357, hlam]
                        · linarith only [h0, h5354, hlam]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        rcases p5330_3 (m.d 0 1) (by simp) with h5364 | h5364
                        · rcases p5330_3 (m.d 0 2) (by simp) with h5365 | h5365
                          · linarith only [h4, h5365, hlam]
                          · rcases p5330_3 (m.d 0 3) (by simp) with h5367 | h5367
                            · rcases p5330_3 (m.d 0 4) (by simp) with h5368 | h5368
                              · linarith only [h4106, h5368, hlam]
                              · rcases p5330_3 (m.d 0 5) (by simp) with h5370 | h5370
                                · linarith only [h4107, h5370, hlam]
                                · linarith only [h4108, h5370, hlam]
                            · linarith only [h4106, h5367, hlam]
                        · linarith only [h2, h5364, hlam]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h4107, h4952, h4953, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5330_1]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h2, hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h0, h4108, h5325, h5327, hc12, hc23, hlam, hphi, p5330_1]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h4106, hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h4108, hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h3, hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h0, h4108, h5325, h5327, hc12, hc23, hlam, hphi, p5330_1]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h4107, hlam, p5330_0]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [h0, h3476, h4108, h5325, h5327, hc12, hc23, hlam, hphi, p5330_1]
                      · have p5330_0 := h5330c.1
                        have p5330_1 := h5330c.2.1
                        have p5330_2 := h5330c.2.2.1
                        have p5330_3 := h5330c.2.2.2
                        linarith only [hlam, p5330_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5386 | h5386
                    · linarith only [h4952, h4953, h5327, h5386, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · rcases h0bigk with h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c | h5388c
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        rcases p5388_3 (m.d 0 1) (by simp) with h5390 | h5390
                        · rcases p5388_3 (m.d 0 2) (by simp) with h5391 | h5391
                          · linarith only [h0, h5391, hlam]
                          · rcases p5388_3 (m.d 0 3) (by simp) with h5393 | h5393
                            · linarith only [h1, h5393, hlam]
                            · linarith only [h4, h5393, hlam]
                        · linarith only [h0, h5390, hlam]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h4107, h4953, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5388_1]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        rcases p5388_3 (m.d 0 1) (by simp) with h5398 | h5398
                        · rcases p5388_3 (m.d 0 2) (by simp) with h5399 | h5399
                          · linarith only [h0, h5399, hlam]
                          · rcases p5388_3 (m.d 0 3) (by simp) with h5401 | h5401
                            · linarith only [h1, h5401, hlam]
                            · linarith only [h4106, h5401, hlam]
                        · linarith only [h2, h5398, hlam]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h4107, h4952, h4953, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5388_1]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h0, hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h4, hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h3476, hlam, p5388_1]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h4023, hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h1, hlam, p5388_1]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        rcases p5388_3 (m.d 0 1) (by simp) with h5412 | h5412
                        · rcases p5388_3 (m.d 0 2) (by simp) with h5413 | h5413
                          · linarith only [h4, h5413, hlam]
                          · rcases p5388_3 (m.d 0 3) (by simp) with h5415 | h5415
                            · rcases p5388_3 (m.d 0 4) (by simp) with h5416 | h5416
                              · linarith only [h4106, h5416, hlam]
                              · linarith only [h3476, h5416, hlam]
                            · linarith only [h4, h5415, hlam]
                        · linarith only [h0, h5412, hlam]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        rcases p5388_3 (m.d 0 1) (by simp) with h5422 | h5422
                        · rcases p5388_3 (m.d 0 2) (by simp) with h5423 | h5423
                          · linarith only [h4, h5423, hlam]
                          · rcases p5388_3 (m.d 0 3) (by simp) with h5425 | h5425
                            · rcases p5388_3 (m.d 0 4) (by simp) with h5426 | h5426
                              · linarith only [h4106, h5426, hlam]
                              · rcases p5388_3 (m.d 0 5) (by simp) with h5428 | h5428
                                · linarith only [h4107, h5428, hlam]
                                · linarith only [h4108, h5428, hlam]
                            · linarith only [h4106, h5425, hlam]
                        · linarith only [h2, h5422, hlam]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h4107, h4952, h4953, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5388_1]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h2, hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h0, h3476, h5327, hc12, hc45, hlam, hphi, ht23, ht34, p5388_1]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h4106, hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h4108, hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h3, hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        rcases p5388_3 (m.d 0 1) (by simp) with h5440 | h5440
                        · rcases p5388_3 (m.d 0 2) (by simp) with h5441 | h5441
                          · linarith only [h4023, h5441, hlam]
                          · rcases p5388_3 (m.d 0 3) (by simp) with h5443 | h5443
                            · rcases p5388_3 (m.d 0 4) (by simp) with h5444 | h5444
                              · linarith only [h4108, h5444, hlam]
                              · linarith only [h3476, h5444, hlam]
                            · linarith only [h4, h5443, hlam]
                        · linarith only [h0, h5440, hlam]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [h4107, hlam, p5388_0]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        rcases p5388_3 (m.d 0 1) (by simp) with h5450 | h5450
                        · rcases p5388_3 (m.d 0 2) (by simp) with h5451 | h5451
                          · linarith only [h4023, h5451, hlam]
                          · rcases p5388_3 (m.d 0 3) (by simp) with h5453 | h5453
                            · rcases p5388_3 (m.d 0 4) (by simp) with h5454 | h5454
                              · linarith only [h4108, h5454, hlam]
                              · rcases p5388_3 (m.d 0 5) (by simp) with h5456 | h5456
                                · rcases h2bigk with h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c | h5457c
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h3476, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5388_1, p5457_1]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h4, hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h3476, hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h4023, hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h0, hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h4946, hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h4948, hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h4950, hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    rcases p5457_3 (m.d 0 2) (by simp) with h5468 | h5468
                                    · linarith only [h5468, hlam, p5457_0]
                                    · rcases p5457_3 (m.d 1 2) (by simp) with h5470 | h5470
                                      · linarith only [h4946, h5470, hlam]
                                      · rcases p5457_3 (m.d 2 3) (by simp) with h5472 | h5472
                                        · rcases p5457_3 (m.d 2 4) (by simp) with h5473 | h5473
                                          · linarith only [h5325, h5473, hlam]
                                          · linarith only [h3476, h5473, hlam]
                                        · linarith only [h5472, hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    rcases p5457_3 (m.d 0 2) (by simp) with h5477 | h5477
                                    · linarith only [h4, h5477, hlam]
                                    · linarith only [h0, h5477, hlam]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h3476, hc02, hc23, hlam, hphi, p5457_1]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h4023, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5388_1, p5457_1]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h0, h5327, hc12, hc45, hlam, hphi, ht23, ht34, p5457_1]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h5327, hc12, hc45, hlam, hphi, ht23, ht34, p5457_1]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h5325, hlam, p5457_1]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [hlam, p5457_0]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h5327, hlam, p5457_1]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    rcases p5457_3 (m.d 0 2) (by simp) with h5488 | h5488
                                    · linarith only [h5488, hlam, p5457_0]
                                    · rcases p5457_3 (m.d 1 2) (by simp) with h5490 | h5490
                                      · linarith only [h4950, h5490, hlam]
                                      · rcases p5457_3 (m.d 2 3) (by simp) with h5492 | h5492
                                        · rcases p5457_3 (m.d 2 4) (by simp) with h5493 | h5493
                                          · linarith only [h5327, h5493, hlam]
                                          · linarith only [h3476, h5493, hlam]
                                        · linarith only [h4, h5492, hlam]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    rcases p5457_3 (m.d 0 2) (by simp) with h5497 | h5497
                                    · linarith only [h4023, h5497, hlam]
                                    · linarith only [h0, h5497, hlam]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h5326, hlam, p5457_1]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [h0, h3476, hc12, hc25, hlam, hphi, p5457_1]
                                  · have p5457_0 := h5457c.1
                                    have p5457_1 := h5457c.2.1
                                    have p5457_2 := h5457c.2.2.1
                                    have p5457_3 := h5457c.2.2.2
                                    linarith only [hlam, p5457_0]
                                · linarith only [h4108, h5456, hlam]
                            · linarith only [h4106, h5453, hlam]
                        · linarith only [h2, h5450, hlam]
                      · have p5388_0 := h5388c.1
                        have p5388_1 := h5388c.2.1
                        have p5388_2 := h5388c.2.2.1
                        have p5388_3 := h5388c.2.2.2
                        linarith only [hlam, p5388_0]
                · linarith only [h4, h4107, h5326, hlam]
              · linarith only [h4, h4107, h4952, h4953, h5325, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5509 | h5509
          · linarith only [h4106, h4952, h5509, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5511 | h5511
            · linarith only [h4106, h4108, h4952, h5511, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5513 | h5513
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5514 | h5514
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5515 | h5515
                  · linarith only [h4106, h4108, h4946, h4952, h5515, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5517 | h5517
                    · linarith only [h0, h3476, h5515, h5517, hc12, hc34, hlam, hphi, ht23]
                    · rcases h0bigk with h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        rcases p5519_3 (m.d 0 1) (by simp) with h5521 | h5521
                        · rcases p5519_3 (m.d 0 2) (by simp) with h5522 | h5522
                          · linarith only [h0, h5522, hlam]
                          · rcases p5519_3 (m.d 0 3) (by simp) with h5524 | h5524
                            · linarith only [h1, h5524, hlam]
                            · linarith only [h4, h5524, hlam]
                        · linarith only [h0, h5521, hlam]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h4106, h4946, h4952, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5519_1]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        rcases p5519_3 (m.d 0 1) (by simp) with h5529 | h5529
                        · rcases p5519_3 (m.d 0 2) (by simp) with h5530 | h5530
                          · linarith only [h0, h5530, hlam]
                          · rcases p5519_3 (m.d 0 3) (by simp) with h5532 | h5532
                            · linarith only [h1, h5532, hlam]
                            · linarith only [h4106, h5532, hlam]
                        · linarith only [h2, h5529, hlam]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        rcases p5519_3 (m.d 0 1) (by simp) with h5536 | h5536
                        · rcases p5519_3 (m.d 0 2) (by simp) with h5537 | h5537
                          · linarith only [h0, h5537, hlam]
                          · rcases p5519_3 (m.d 0 3) (by simp) with h5539 | h5539
                            · linarith only [h1, h5539, hlam]
                            · linarith only [h4107, h5539, hlam]
                        · linarith only [h3, h5536, hlam]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h0, hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h4, hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h3476, hlam, p5519_1]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h4023, hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h1, hlam, p5519_1]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        rcases p5519_3 (m.d 0 1) (by simp) with h5549 | h5549
                        · rcases p5519_3 (m.d 0 2) (by simp) with h5550 | h5550
                          · linarith only [h4, h5550, hlam]
                          · rcases p5519_3 (m.d 0 3) (by simp) with h5552 | h5552
                            · rcases p5519_3 (m.d 0 4) (by simp) with h5553 | h5553
                              · linarith only [h4106, h5553, hlam]
                              · linarith only [h3476, h5553, hlam]
                            · linarith only [h4, h5552, hlam]
                        · linarith only [h0, h5549, hlam]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h4, h4106, h4946, h4952, hc12, hc23, hlam, hphi, p5519_1]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h4, h4106, h4108, h4946, h4952, hc12, hc23, hlam, hphi, p5519_1]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h2, hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h3476, h5515, hc02, hc45, hlam, hphi, ht23, ht34, p5519_1]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h4106, hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h4108, hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h3, hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        rcases p5519_3 (m.d 0 1) (by simp) with h5567 | h5567
                        · rcases p5519_3 (m.d 0 2) (by simp) with h5568 | h5568
                          · linarith only [h4023, h5568, hlam]
                          · rcases p5519_3 (m.d 0 3) (by simp) with h5570 | h5570
                            · rcases p5519_3 (m.d 0 4) (by simp) with h5571 | h5571
                              · linarith only [h4108, h5571, hlam]
                              · linarith only [h3476, h5571, hlam]
                            · linarith only [h4, h5570, hlam]
                        · linarith only [h0, h5567, hlam]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h4107, hlam, p5519_0]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [h4023, h4106, h4946, h4952, h5515, hc12, hc45, hlam, hphi, ht23, ht34, p5519_1]
                      · have p5519_0 := h5519c.1
                        have p5519_1 := h5519c.2.1
                        have p5519_2 := h5519c.2.2.1
                        have p5519_3 := h5519c.2.2.2
                        linarith only [hlam, p5519_0]
                · linarith only [h4, h4107, h5514, hlam]
              · linarith only [h4, h4106, h5513, hlam]

set_option maxHeartbeats 5090000 in
set_option maxHeartbeats 5090000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg3476 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg4023 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4106 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4107 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h3476 := hg3476
  have h4023 := hg4023
  rcases m.htr 0 4 5 (by decide) (by decide) with h4108 | h4108
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg3476 hg4023 h4106 h4107 h4108
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg3476 hg4023 h4106 h4107 h4108

end R2N4
