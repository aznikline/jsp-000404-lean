import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S23

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h8411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h8412 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8413 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8414 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8415 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h8957 | h8957
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8958 | h8958
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8959 | h8959
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8960 | h8960
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8961 | h8961
          · linarith only [h8415, h8957, h8961, hc13, hlam, hphi, ht01, u0ehi4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8963 | h8963
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8964 | h8964
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8965 | h8965
                · linarith only [h8410, h8415, h8957, h8959, h8965, hc01, hlam, hphi, u0ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8967 | h8967
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8968 | h8968
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8969 | h8969
                      · rcases h2bigk with h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c | h8970c
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h0, hlam, p8970_1]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          rcases p8970_3 (m.d 0 2) (by simp) with h8973 | h8973
                          · rcases p8970_3 (m.d 1 2) (by simp) with h8974 | h8974
                            · rcases p8970_3 (m.d 2 3) (by simp) with h8975 | h8975
                              · linarith only [h8975, hlam, p8970_0]
                              · rcases p8970_3 (m.d 2 4) (by simp) with h8977 | h8977
                                · linarith only [h8413, h8977, hlam]
                                · linarith only [h8965, h8977, hlam]
                            · linarith only [h8959, h8974, hlam]
                          · linarith only [h8973, hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          rcases p8970_3 (m.d 0 2) (by simp) with h8982 | h8982
                          · rcases p8970_3 (m.d 1 2) (by simp) with h8983 | h8983
                            · rcases p8970_3 (m.d 2 3) (by simp) with h8984 | h8984
                              · linarith only [h8412, h8984, hlam]
                              · rcases p8970_3 (m.d 2 4) (by simp) with h8986 | h8986
                                · linarith only [h8986, hlam, p8970_0]
                                · rcases p8970_3 (m.d 2 5) (by simp) with h8988 | h8988
                                  · linarith only [h8414, h8988, hlam]
                                  · rcases h3bigk with h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c | h8990c
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8415, hc13, hc34, hlam, hphi, p8990_1]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8415, hc23, hc34, hlam, hphi, p8990_1]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8415, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      rcases p8990_3 (m.d 0 3) (by simp) with h8995 | h8995
                                      · rcases p8990_3 (m.d 1 3) (by simp) with h8996 | h8996
                                        · linarith only [h8410, h8996, hlam]
                                        · linarith only [h8963, h8996, hlam]
                                      · linarith only [h8995, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8410, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h0, h8410, h8967, h8969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8990_1]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8961, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h0, h8410, h8969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8990_1]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8412, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8959, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8965, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h0, h8410, h8959, h8969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8990_1]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p8990_1, u0ehi2]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      rcases p8990_3 (m.d 0 3) (by simp) with h9011 | h9011
                                      · linarith only [h8415, h9011, hlam]
                                      · linarith only [h8410, h9011, hlam]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      rcases p8990_3 (m.d 0 3) (by simp) with h9014 | h9014
                                      · linarith only [h8415, h9014, hlam]
                                      · linarith only [h8412, h9014, hlam]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      rcases p8990_3 (m.d 0 3) (by simp) with h9018 | h9018
                                      · linarith only [h8415, h9018, hlam]
                                      · linarith only [h8957, h9018, hlam]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8957, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8963, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8967, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [h8969, hlam, p8990_0]
                                    · have p8990_0 := h8990c.1
                                      have p8990_1 := h8990c.2.1
                                      have p8990_2 := h8990c.2.2.1
                                      have p8990_3 := h8990c.2.2.2
                                      linarith only [hlam, p8990_0]
                            · linarith only [h0, h8983, hlam, p8970_1]
                          · linarith only [h8982, hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          rcases p8970_3 (m.d 0 2) (by simp) with h9028 | h9028
                          · rcases p8970_3 (m.d 1 2) (by simp) with h9029 | h9029
                            · rcases p8970_3 (m.d 2 3) (by simp) with h9030 | h9030
                              · linarith only [h8412, h9030, hlam]
                              · linarith only [h8967, h9030, hlam]
                            · linarith only [h8960, h9029, hlam]
                          · linarith only [h9028, hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p8970_1, u0ehi1]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          rcases p8970_3 (m.d 0 2) (by simp) with h9037 | h9037
                          · linarith only [h0, h9037, hlam]
                          · linarith only [h8412, h9037, hlam]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          rcases p8970_3 (m.d 0 2) (by simp) with h9040 | h9040
                          · linarith only [h0, h9040, hlam]
                          · linarith only [h8413, h9040, hlam]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          rcases p8970_3 (m.d 0 2) (by simp) with h9043 | h9043
                          · linarith only [h0, h9043, hlam]
                          · linarith only [h8414, h9043, hlam]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h8412, hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h8959, hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h8965, hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h0, h8410, h8959, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8970_1]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h8413, hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p8970_1]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h0, h8413, h8967, h8969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8970_1]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          rcases p8970_3 (m.d 0 2) (by simp) with h9055 | h9055
                          · rcases p8970_3 (m.d 1 2) (by simp) with h9056 | h9056
                            · rcases p8970_3 (m.d 2 3) (by simp) with h9057 | h9057
                              · linarith only [h8965, h9057, hlam]
                              · linarith only [h8967, h9057, hlam]
                            · linarith only [h8960, h9056, hlam]
                          · linarith only [h8414, h9055, hlam]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h8414, hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h8960, hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h8967, hlam, p8970_1]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [h8968, hlam, p8970_0]
                        · have p8970_0 := h8970c.1
                          have p8970_1 := h8970c.2.1
                          have p8970_2 := h8970c.2.2.1
                          have p8970_3 := h8970c.2.2.2
                          linarith only [hlam, p8970_0]
                      · linarith only [h8415, h8957, h8969, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                    · linarith only [h0, h8410, h8963, h8964, h8965, h8967, h8968, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h8415, h8957, h8967, hc23, hc34, hlam, hphi]
              · linarith only [h8961, h8963, h8964, hlam]
            · linarith only [h8415, h8957, h8963, hc13, hc34, hlam, hphi]
        · linarith only [h0, h8960, hc25, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h8959, hc23, hlam, hphi, ht01, ht12, u0ehi0]
    · linarith only [h8415, h8957, h8958, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9075 | h9075
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9076 | h9076
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9077 | h9077
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9078 | h9078
          · linarith only [h8410, h8415, h9078, hc01, hlam, hphi, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9080 | h9080
            · linarith only [h0, h8410, h8957, h9080, hc12, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9082 | h9082
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9083 | h9083
                · linarith only [h0, h8411, h8415, h9076, h9080, h9083, hc12, hlam, hphi, ht01, u0ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9085 | h9085
                  · linarith only [h0, h8411, h8957, h9076, h9080, h9085, hc12, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9087 | h9087
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9088 | h9088
                      · rcases h2bigk with h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c | h9089c
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h0, hlam, p9089_1]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          rcases p9089_3 (m.d 0 2) (by simp) with h9092 | h9092
                          · rcases p9089_3 (m.d 1 2) (by simp) with h9093 | h9093
                            · rcases p9089_3 (m.d 2 3) (by simp) with h9094 | h9094
                              · linarith only [h9094, hlam, p9089_0]
                              · rcases p9089_3 (m.d 2 4) (by simp) with h9096 | h9096
                                · linarith only [h8413, h9096, hlam]
                                · linarith only [h9083, h9096, hlam]
                            · linarith only [h9076, h9093, hlam]
                          · linarith only [h9092, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          rcases p9089_3 (m.d 0 2) (by simp) with h9101 | h9101
                          · rcases p9089_3 (m.d 1 2) (by simp) with h9102 | h9102
                            · rcases p9089_3 (m.d 2 3) (by simp) with h9103 | h9103
                              · linarith only [h8412, h9103, hlam]
                              · rcases p9089_3 (m.d 2 4) (by simp) with h9105 | h9105
                                · linarith only [h9105, hlam, p9089_0]
                                · rcases p9089_3 (m.d 2 5) (by simp) with h9107 | h9107
                                  · linarith only [h8414, h9107, hlam]
                                  · rcases h3bigk with h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h8957, h9088, hc13, hc34, hlam, hphi, p9109_1]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h8957, h9088, hc23, hc34, hlam, hphi, p9109_1]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h8415, hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h8957, hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h8410, hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h0, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9109_1]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h9078, hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h9080, hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h8412, hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h9076, hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h9083, hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h9085, hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p9109_1, u0ehi2]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      rcases p9109_3 (m.d 0 3) (by simp) with h9126 | h9126
                                      · linarith only [h8415, h9126, hlam]
                                      · linarith only [h8410, h9126, hlam]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      rcases p9109_3 (m.d 0 3) (by simp) with h9129 | h9129
                                      · linarith only [h8415, h9129, hlam]
                                      · linarith only [h8412, h9129, hlam]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h8957, hc34, hlam, hphi, ht01, ht12, ht23, p9109_1, u0ehi2]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p9109_1, u0ehi2]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      rcases p9109_3 (m.d 0 3) (by simp) with h9135 | h9135
                                      · linarith only [h8957, h9135, hlam]
                                      · linarith only [h8410, h9135, hlam]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      rcases p9109_3 (m.d 0 3) (by simp) with h9138 | h9138
                                      · linarith only [h8957, h9138, hlam]
                                      · linarith only [h8412, h9138, hlam]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [h9088, hlam, p9109_0]
                                    · have p9109_0 := h9109c.1
                                      have p9109_1 := h9109c.2.1
                                      have p9109_2 := h9109c.2.2.1
                                      have p9109_3 := h9109c.2.2.2
                                      linarith only [hlam, p9109_0]
                            · linarith only [h0, h9102, hlam, p9089_1]
                          · linarith only [h9101, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          rcases p9089_3 (m.d 0 2) (by simp) with h9145 | h9145
                          · rcases p9089_3 (m.d 1 2) (by simp) with h9146 | h9146
                            · rcases p9089_3 (m.d 2 3) (by simp) with h9147 | h9147
                              · linarith only [h8412, h9147, hlam]
                              · rcases p9089_3 (m.d 2 4) (by simp) with h9149 | h9149
                                · linarith only [h8413, h9149, hlam]
                                · linarith only [h9087, h9149, hlam]
                            · linarith only [h9077, h9146, hlam]
                          · linarith only [h9145, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p9089_1, u0ehi1]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          rcases p9089_3 (m.d 0 2) (by simp) with h9156 | h9156
                          · linarith only [h0, h9156, hlam]
                          · linarith only [h8412, h9156, hlam]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          rcases p9089_3 (m.d 0 2) (by simp) with h9159 | h9159
                          · linarith only [h0, h9159, hlam]
                          · linarith only [h8413, h9159, hlam]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          rcases p9089_3 (m.d 0 2) (by simp) with h9162 | h9162
                          · linarith only [h0, h9162, hlam]
                          · linarith only [h8414, h9162, hlam]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h8412, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h9076, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h9083, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h9085, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h8413, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p9089_1]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          rcases p9089_3 (m.d 0 2) (by simp) with h9172 | h9172
                          · rcases p9089_3 (m.d 1 2) (by simp) with h9173 | h9173
                            · rcases p9089_3 (m.d 2 3) (by simp) with h9174 | h9174
                              · linarith only [h9083, h9174, hlam]
                              · rcases p9089_3 (m.d 2 4) (by simp) with h9176 | h9176
                                · rcases p9089_3 (m.d 2 5) (by simp) with h9177 | h9177
                                  · linarith only [h9087, h9177, hlam]
                                  · linarith only [h9085, h9177, hlam]
                                · linarith only [h9083, h9176, hlam]
                            · linarith only [h9076, h9173, hlam]
                          · linarith only [h8412, h9172, hlam]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          rcases p9089_3 (m.d 0 2) (by simp) with h9184 | h9184
                          · rcases p9089_3 (m.d 1 2) (by simp) with h9185 | h9185
                            · rcases p9089_3 (m.d 2 3) (by simp) with h9186 | h9186
                              · linarith only [h9083, h9186, hlam]
                              · rcases p9089_3 (m.d 2 4) (by simp) with h9188 | h9188
                                · rcases p9089_3 (m.d 2 5) (by simp) with h9189 | h9189
                                  · linarith only [h9087, h9189, hlam]
                                  · rcases h3bigk with h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c | h9191c
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h8415, hc13, hc34, hlam, hphi, p9191_1]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h8415, hc23, hc34, hlam, hphi, p9191_1]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h8415, hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h8957, hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h8410, hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h0, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9191_1]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h9078, hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h9080, hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h8412, hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h9076, hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h9083, hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h9085, hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p9191_1, u0ehi2]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      rcases p9191_3 (m.d 0 3) (by simp) with h9208 | h9208
                                      · linarith only [h8415, h9208, hlam]
                                      · linarith only [h8410, h9208, hlam]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      rcases p9191_3 (m.d 0 3) (by simp) with h9211 | h9211
                                      · linarith only [h8415, h9211, hlam]
                                      · linarith only [h8412, h9211, hlam]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h0, h8413, h8957, h9085, hc12, hc23, hc34, hlam, hphi, ht01, p9089_1, p9191_1, u0ehi2]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h0, h8413, h9085, hc12, hc23, hc35, hlam, hphi, ht01, p9089_1, p9191_1, u0ehi2]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      rcases p9191_3 (m.d 0 3) (by simp) with h9217 | h9217
                                      · linarith only [h8957, h9217, hlam]
                                      · linarith only [h8410, h9217, hlam]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      rcases p9191_3 (m.d 0 3) (by simp) with h9220 | h9220
                                      · linarith only [h8957, h9220, hlam]
                                      · linarith only [h8412, h9220, hlam]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [h9088, hlam, p9191_0]
                                    · have p9191_0 := h9191c.1
                                      have p9191_1 := h9191c.2.1
                                      have p9191_2 := h9191c.2.2.1
                                      have p9191_3 := h9191c.2.2.2
                                      linarith only [hlam, p9191_0]
                                · linarith only [h9087, h9188, hlam]
                            · linarith only [h9077, h9185, hlam]
                          · linarith only [h8414, h9184, hlam]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h8414, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h9077, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h0, h8411, h9077, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9089_1]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [h9087, hlam, p9089_0]
                        · have p9089_0 := h9089c.1
                          have p9089_1 := h9089c.2.1
                          have p9089_2 := h9089c.2.2.1
                          have p9089_3 := h9089c.2.2.2
                          linarith only [hlam, p9089_0]
                      · linarith only [h8415, h9088, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9234 | h9234
                      · rcases h2bigk with h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c | h9235c
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h0, hlam, p9235_1]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          rcases p9235_3 (m.d 0 2) (by simp) with h9238 | h9238
                          · rcases p9235_3 (m.d 1 2) (by simp) with h9239 | h9239
                            · rcases p9235_3 (m.d 2 3) (by simp) with h9240 | h9240
                              · linarith only [h9240, hlam, p9235_0]
                              · rcases p9235_3 (m.d 2 4) (by simp) with h9242 | h9242
                                · linarith only [h8413, h9242, hlam]
                                · linarith only [h9083, h9242, hlam]
                            · linarith only [h9076, h9239, hlam]
                          · linarith only [h9238, hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          rcases p9235_3 (m.d 0 2) (by simp) with h9247 | h9247
                          · rcases p9235_3 (m.d 1 2) (by simp) with h9248 | h9248
                            · rcases p9235_3 (m.d 2 3) (by simp) with h9249 | h9249
                              · linarith only [h8412, h9249, hlam]
                              · rcases p9235_3 (m.d 2 4) (by simp) with h9251 | h9251
                                · linarith only [h9251, hlam, p9235_0]
                                · rcases p9235_3 (m.d 2 5) (by simp) with h9253 | h9253
                                  · linarith only [h8414, h9253, hlam]
                                  · linarith only [h9087, h9253, hlam]
                            · linarith only [h0, h8411, h9082, h9087, h9248, hlam]
                          · linarith only [h9247, hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          rcases p9235_3 (m.d 0 2) (by simp) with h9258 | h9258
                          · rcases p9235_3 (m.d 1 2) (by simp) with h9259 | h9259
                            · rcases p9235_3 (m.d 2 3) (by simp) with h9260 | h9260
                              · linarith only [h8412, h9260, hlam]
                              · rcases p9235_3 (m.d 2 4) (by simp) with h9262 | h9262
                                · linarith only [h8413, h9262, hlam]
                                · rcases p9235_3 (m.d 2 5) (by simp) with h9264 | h9264
                                  · linarith only [h9264, hlam, p9235_0]
                                  · rcases h3bigk with h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h8415, hc13, hc34, hlam, hphi, p9266_1]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h8415, hc23, hc34, hlam, hphi, p9266_1]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h8415, hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h8957, hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h8410, hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h0, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9266_1]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h9078, hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h9080, hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h8412, hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h9076, hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h9083, hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h9085, hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p9266_1, u0ehi2]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      rcases p9266_3 (m.d 0 3) (by simp) with h9283 | h9283
                                      · linarith only [h8415, h9283, hlam]
                                      · linarith only [h8410, h9283, hlam]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      rcases p9266_3 (m.d 0 3) (by simp) with h9286 | h9286
                                      · linarith only [h8415, h9286, hlam]
                                      · linarith only [h8412, h9286, hlam]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h0, h8411, h8957, h9082, h9083, h9087, hc12, hc23, hc34, hlam, hphi, ht01, p9266_1, u0ehi2]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h0, h8411, h9082, h9083, h9087, hc12, hc23, hc35, hlam, hphi, ht01, p9266_1, u0ehi2]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      rcases p9266_3 (m.d 0 3) (by simp) with h9292 | h9292
                                      · linarith only [h8957, h9292, hlam]
                                      · linarith only [h8410, h9292, hlam]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      rcases p9266_3 (m.d 0 3) (by simp) with h9295 | h9295
                                      · linarith only [h8957, h9295, hlam]
                                      · linarith only [h8412, h9295, hlam]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [h9234, hlam, p9266_0]
                                    · have p9266_0 := h9266c.1
                                      have p9266_1 := h9266c.2.1
                                      have p9266_2 := h9266c.2.2.1
                                      have p9266_3 := h9266c.2.2.2
                                      linarith only [hlam, p9266_0]
                            · linarith only [h9077, h9259, hlam]
                          · linarith only [h9258, hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p9235_1, u0ehi1]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h0, h8411, h9082, h9083, h9087, hlam, p9235_2]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h0, h8411, h9082, h9087, hlam, p9235_2]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          rcases p9235_3 (m.d 0 2) (by simp) with h9306 | h9306
                          · linarith only [h0, h9306, hlam]
                          · linarith only [h8414, h9306, hlam]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h8412, hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h9076, hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h9083, hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h9085, hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h8413, hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h0, h8411, h9082, h9087, hlam, p9235_1]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h0, h8411, h9082, h9087, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9235_1]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h9087, hlam, p9235_1]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h8414, hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h9077, hlam, p9235_0]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h0, h8411, h9077, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9235_1]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [h0, h8411, h9082, h9087, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9235_1]
                        · have p9235_0 := h9235c.1
                          have p9235_1 := h9235c.2.1
                          have p9235_2 := h9235c.2.2.1
                          have p9235_3 := h9235c.2.2.2
                          linarith only [hlam, p9235_0]
                      · linarith only [h0, h8411, h8415, h9082, h9234, hc12, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9325 | h9325
                · linarith only [h8415, h9325, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9327 | h9327
                  · linarith only [h8957, h9075, h9076, h9078, h9082, h9327, hc04, hlam, hphi, u0ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9329 | h9329
                    · linarith only [h9077, h9082, h9329, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9331 | h9331
                      · rcases h2bigk with h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c | h9332c
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h0, hlam, p9332_1]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          rcases p9332_3 (m.d 0 2) (by simp) with h9335 | h9335
                          · rcases p9332_3 (m.d 1 2) (by simp) with h9336 | h9336
                            · rcases p9332_3 (m.d 2 3) (by simp) with h9337 | h9337
                              · linarith only [h9337, hlam, p9332_0]
                              · rcases p9332_3 (m.d 2 4) (by simp) with h9339 | h9339
                                · linarith only [h8413, h9339, hlam]
                                · linarith only [h9325, h9339, hlam]
                            · linarith only [h9076, h9336, hlam]
                          · linarith only [h9335, hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          rcases p9332_3 (m.d 0 2) (by simp) with h9344 | h9344
                          · rcases p9332_3 (m.d 1 2) (by simp) with h9345 | h9345
                            · rcases p9332_3 (m.d 2 3) (by simp) with h9346 | h9346
                              · linarith only [h8412, h9346, hlam]
                              · rcases p9332_3 (m.d 2 4) (by simp) with h9348 | h9348
                                · linarith only [h9348, hlam, p9332_0]
                                · rcases p9332_3 (m.d 2 5) (by simp) with h9350 | h9350
                                  · linarith only [h8414, h9350, hlam]
                                  · linarith only [h9329, h9350, hlam]
                            · linarith only [h0, h8415, h9075, h9329, h9345, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h9344, hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          rcases p9332_3 (m.d 0 2) (by simp) with h9355 | h9355
                          · rcases p9332_3 (m.d 1 2) (by simp) with h9356 | h9356
                            · rcases p9332_3 (m.d 2 3) (by simp) with h9357 | h9357
                              · linarith only [h8412, h9357, hlam]
                              · rcases p9332_3 (m.d 2 4) (by simp) with h9359 | h9359
                                · linarith only [h8413, h9359, hlam]
                                · rcases p9332_3 (m.d 2 5) (by simp) with h9361 | h9361
                                  · linarith only [h9361, hlam, p9332_0]
                                  · rcases h3bigk with h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c | h9363c
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h8957, h9076, hc23, hc35, hlam, hphi, p9363_1]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h8957, hc23, hc35, hlam, hphi, p9363_1]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h8415, hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h8957, hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h8410, hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h0, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9363_1]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h9078, hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h9080, hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h8412, hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h9076, hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h9325, hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h9327, hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p9363_1, u0ehi2]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      rcases p9363_3 (m.d 0 3) (by simp) with h9380 | h9380
                                      · linarith only [h8415, h9380, hlam]
                                      · linarith only [h8410, h9380, hlam]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      rcases p9363_3 (m.d 0 3) (by simp) with h9383 | h9383
                                      · linarith only [h8415, h9383, hlam]
                                      · linarith only [h8412, h9383, hlam]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h8957, hc34, hlam, hphi, ht01, ht12, ht23, p9363_1, u0ehi2]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p9363_1, u0ehi2]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      rcases p9363_3 (m.d 0 3) (by simp) with h9389 | h9389
                                      · linarith only [h8957, h9389, hlam]
                                      · linarith only [h8410, h9389, hlam]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      rcases p9363_3 (m.d 0 3) (by simp) with h9392 | h9392
                                      · linarith only [h8957, h9392, hlam]
                                      · linarith only [h8412, h9392, hlam]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [h9331, hlam, p9363_0]
                                    · have p9363_0 := h9363c.1
                                      have p9363_1 := h9363c.2.1
                                      have p9363_2 := h9363c.2.2.1
                                      have p9363_3 := h9363c.2.2.2
                                      linarith only [hlam, p9363_0]
                            · linarith only [h9077, h9356, hlam]
                          · linarith only [h9355, hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h8413, h9075, h9078, h9082, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9332_1]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          rcases p9332_3 (m.d 0 2) (by simp) with h9401 | h9401
                          · linarith only [h0, h9401, hlam]
                          · linarith only [h8412, h9401, hlam]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          rcases p9332_3 (m.d 0 2) (by simp) with h9404 | h9404
                          · linarith only [h0, h9404, hlam]
                          · linarith only [h8413, h9404, hlam]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          rcases p9332_3 (m.d 0 2) (by simp) with h9407 | h9407
                          · linarith only [h0, h9407, hlam]
                          · linarith only [h8414, h9407, hlam]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h8412, hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h9076, hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h9325, hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h9327, hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h8413, hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p9332_1]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h0, h8411, h9077, h9329, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9332_1]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h9329, hlam, p9332_1]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h8414, hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h9077, hlam, p9332_0]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h0, h8411, h9077, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9332_1]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [h0, h8411, h9077, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9332_1]
                        · have p9332_0 := h9332c.1
                          have p9332_1 := h9332c.2.1
                          have p9332_2 := h9332c.2.2.1
                          have p9332_3 := h9332c.2.2.2
                          linarith only [hlam, p9332_0]
                      · linarith only [h8415, h9075, h9331, hc04, hlam, hphi, u0ehi2]
        · linarith only [h0, h9077, hc25, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h8411, h8957, h9076, hc23, hlam, hphi, ht01, ht12, u0ehi2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9428 | h9428
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9429 | h9429
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9430 | h9430
          · linarith only [h8410, h8415, h9430, hc01, hlam, hphi, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9432 | h9432
            · linarith only [h0, h8410, h8957, h9432, hc12, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9434 | h9434
              · linarith only [h8415, h9075, h9434, hc14, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9436 | h9436
                · linarith only [h0, h8411, h8415, h9428, h9430, h9434, h9436, hc12, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9438 | h9438
                  · linarith only [h0, h8411, h8957, h9428, h9430, h9434, h9438, hc12, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9440 | h9440
                    · linarith only [h8415, h9075, h9440, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9442 | h9442
                      · linarith only [h8415, h9075, h9442, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h8415, h9442, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
        · linarith only [h0, h9429, hc25, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h8411, h8415, h9075, h9428, hc23, hlam, hphi, ht01, ht12, u0ehi2]

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h8411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h8412 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8413 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8414 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h8415 | h8415
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h8410 h8411 h8412 h8413 h8414 h8415
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h8410 h8411 h8412 h8413 h8414 h8415

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h8411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h8412 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8413 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8414 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  linarith only [h0, h8411, h8414, hlam]

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h8411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h8412 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8413 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h8414 | h8414
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h8410 h8411 h8412 h8413 h8414
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h8410 h8411 h8412 h8413 h8414

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h8411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h8412 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8413 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h9448 | h9448
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9449 | h9449
    · linarith only [h0, h8410, h8413, h9449, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9451 | h9451
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9452 | h9452
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9453 | h9453
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9454 | h9454
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9455 | h9455
              · linarith only [h0, h8410, h8413, h9449, h9455, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9457 | h9457
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9458 | h9458
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9459 | h9459
                    · linarith only [h0, h8410, h8413, h9449, h9451, h9453, h9459, hc24, hlam, hphi, ht01, ht12, u0ehi4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9461 | h9461
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9462 | h9462
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9463 | h9463
                          · rcases h2bigk with h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c | h9464c
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h0, hlam, p9464_1]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h8413, h9459, hc23, hc34, hlam, hphi, p9464_1]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h8413, hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              rcases p9464_3 (m.d 0 2) (by simp) with h9469 | h9469
                              · rcases p9464_3 (m.d 1 2) (by simp) with h9470 | h9470
                                · rcases p9464_3 (m.d 2 3) (by simp) with h9471 | h9471
                                  · linarith only [h8412, h9471, hlam]
                                  · linarith only [h9461, h9471, hlam]
                                · linarith only [h9454, h9470, hlam]
                              · linarith only [h9469, hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, p9464_1, u0ehi0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              rcases p9464_3 (m.d 0 2) (by simp) with h9478 | h9478
                              · linarith only [h0, h9478, hlam]
                              · linarith only [h8412, h9478, hlam]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h0, h8410, h8413, h9453, h9461, h9463, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9464_1]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              rcases p9464_3 (m.d 0 2) (by simp) with h9482 | h9482
                              · linarith only [h0, h9482, hlam]
                              · linarith only [h9448, h9482, hlam]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h8412, hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h9453, hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h9459, hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h0, h8410, h9453, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p9464_1]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h0, hc24, hlam, hphi, ht01, ht12, p9464_1, u0ehi0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h0, h8410, h9453, h9459, h9461, h9463, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9464_1]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              rcases p9464_3 (m.d 0 2) (by simp) with h9492 | h9492
                              · linarith only [h8413, h9492, hlam]
                              · linarith only [h8412, h9492, hlam]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              rcases p9464_3 (m.d 0 2) (by simp) with h9496 | h9496
                              · linarith only [h8413, h9496, hlam]
                              · linarith only [h9448, h9496, hlam]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h9448, hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h9454, hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h9461, hlam, p9464_1]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [h9462, hlam, p9464_0]
                            · have p9464_0 := h9464c.1
                              have p9464_1 := h9464c.2.1
                              have p9464_2 := h9464c.2.2.1
                              have p9464_3 := h9464c.2.2.2
                              linarith only [hlam, p9464_0]
                          · linarith only [h9449, h9451, h9463, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                        · linarith only [h0, h8410, h8413, h9457, h9458, h9462, hlam]
                      · linarith only [h0, h8410, h8413, h9451, h9459, h9461, hc23, hc34, hlam, hphi]
                  · linarith only [h9455, h9457, h9458, hlam]
                · linarith only [h9449, h9451, h9457, hc13, hc34, hlam, hphi]
            · linarith only [h0, h9454, hc25, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h8410, h9451, h9453, hc23, hlam, hphi, ht01, ht12, u0ehi4]
        · linarith only [h0, h8410, h8413, h9451, h9452, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9512 | h9512
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9513 | h9513
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9514 | h9514
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9515 | h9515
              · linarith only [h8410, h9449, h9515, hc01, hlam, hphi, u0ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9517 | h9517
                · linarith only [h0, h8410, h8413, h9451, h9517, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9519 | h9519
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9520 | h9520
                    · linarith only [h0, h8411, h8413, h9449, h9513, h9517, h9520, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9522 | h9522
                      · linarith only [h0, h8411, h8413, h9451, h9513, h9517, h9520, h9522, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9524 | h9524
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9525 | h9525
                          · rcases h2bigk with h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c | h9526c
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h0, hlam, p9526_1]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h8413, h9520, hc23, hc34, hlam, hphi, p9526_1]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h8413, hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h8413, h9520, h9522, hc23, hc34, hlam, hphi, p9526_1]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, p9526_1, u0ehi0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              rcases p9526_3 (m.d 0 2) (by simp) with h9534 | h9534
                              · linarith only [h0, h9534, hlam]
                              · linarith only [h8412, h9534, hlam]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h0, h8411, h8413, h9451, hc12, hlam, hphi, ht01, p9526_1, u0ehi2]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              rcases p9526_3 (m.d 0 2) (by simp) with h9538 | h9538
                              · linarith only [h0, h9538, hlam]
                              · linarith only [h9448, h9538, hlam]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h8412, hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h9513, hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h9520, hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h9522, hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h0, h8411, h9451, h9520, hc34, hlam, hphi, ht01, ht12, ht23, p9526_1, u0ehi2]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h0, h8411, h9451, h9520, hc34, hlam, hphi, ht01, ht12, ht23, p9526_1, u0ehi2]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              rcases p9526_3 (m.d 0 2) (by simp) with h9548 | h9548
                              · linarith only [h8413, h9548, hlam]
                              · linarith only [h8412, h9548, hlam]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              rcases p9526_3 (m.d 0 2) (by simp) with h9552 | h9552
                              · linarith only [h8413, h9552, hlam]
                              · linarith only [h9448, h9552, hlam]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h9448, hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h9514, hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h8413, h9448, h9520, hc23, hc34, hlam, hphi, p9526_1]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [h9524, hlam, p9526_0]
                            · have p9526_0 := h9526c.1
                              have p9526_1 := h9526c.2.1
                              have p9526_2 := h9526c.2.2.1
                              have p9526_3 := h9526c.2.2.2
                              linarith only [hlam, p9526_0]
                          · linarith only [h8413, h9520, h9525, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                        · linarith only [h0, h8411, h8413, h9519, h9524, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9562 | h9562
                    · linarith only [h8410, h9449, h9513, h9562, hc01, hlam, hphi, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9564 | h9564
                      · linarith only [h0, h8411, h8413, h9451, h9512, h9513, h9515, h9519, h9562, h9564, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9566 | h9566
                        · linarith only [h0, h8411, h8413, h9514, h9515, h9519, h9562, h9566, hc13, hc34, hlam, hphi]
                        · linarith only [h0, h8413, h9566, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]
            · linarith only [h0, h8411, h9451, h9514, hc25, hlam, hphi, ht01, ht12, u0ehi2]
          · linarith only [h0, h8411, h9451, h9513, hc23, hlam, hphi, ht01, ht12, u0ehi2]
        · linarith only [h0, h8411, h8413, h9512, hlam]
  · linarith only [h0, h8411, h9448, hlam]

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h8411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h8412 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h8413 | h8413
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h8410 h8411 h8412 h8413
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h8410 h8411 h8412 h8413

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h8411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h8412 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  linarith only [h0, h8410, h8412, hlam]

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h8411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h8412 | h8412
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h8410 h8411 h8412
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h8410 h8411 h8412

end R2N4
