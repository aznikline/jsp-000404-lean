import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h9938 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h9939 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9940 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9941 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9942 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 1 2 3 (by decide) (by decide) with h10028 | h10028
  · rcases m.htr 1 2 4 (by decide) (by decide) with h10029 | h10029
    · rcases m.htr 1 2 5 (by decide) (by decide) with h10030 | h10030
      · rcases m.htr 1 3 4 (by decide) (by decide) with h10031 | h10031
        · rcases m.htr 1 3 5 (by decide) (by decide) with h10032 | h10032
          · rcases m.htr 1 4 5 (by decide) (by decide) with h10033 | h10033
            · linarith only [h10033, h9935, h9942, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h10035 | h10035
              · rcases m.htr 2 3 5 (by decide) (by decide) with h10036 | h10036
                · rcases m.htr 2 4 5 (by decide) (by decide) with h10037 | h10037
                  · linarith only [h10029, h10037, h9935, h9942, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10039 | h10039
                    · linarith only [h10029, h10035, h10039, h9935, h9942, hlam]
                    · rcases h0bigk with h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h0, hlam, p10041_1]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h6310, hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        rcases p10041_3 (m.d 0 1) (by simp) with h10045 | h10045
                        · rcases p10041_3 (m.d 0 2) (by simp) with h10046 | h10046
                          · rcases p10041_3 (m.d 0 3) (by simp) with h10047 | h10047
                            · rcases p10041_3 (m.d 0 4) (by simp) with h10048 | h10048
                              · linarith only [h10048, h9935, hlam]
                              · rcases p10041_3 (m.d 0 5) (by simp) with h10050 | h10050
                                · linarith only [h10050, h9936, hlam]
                                · linarith only [h10050, h9942, hlam]
                            · linarith only [h10047, h9940, hlam]
                          · linarith only [h10046, h9938, hlam]
                        · linarith only [h10045, h9935, hlam]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        rcases p10041_3 (m.d 0 1) (by simp) with h10056 | h10056
                        · rcases p10041_3 (m.d 0 2) (by simp) with h10057 | h10057
                          · rcases p10041_3 (m.d 0 3) (by simp) with h10058 | h10058
                            · rcases p10041_3 (m.d 0 4) (by simp) with h10059 | h10059
                              · linarith only [h10059, h9935, hlam]
                              · rcases p10041_3 (m.d 0 5) (by simp) with h10061 | h10061
                                · linarith only [h10061, h9936, hlam]
                                · rcases h0emin with h10063 | h10063 | h10063 | h10063 | h10063
                                  · rcases h1bigk with h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c | h10064c
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h0, hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h6310, hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      rcases p10064_3 (m.d 0 1) (by simp) with h10068 | h10068
                                      · rcases p10064_3 (m.d 1 2) (by simp) with h10069 | h10069
                                        · rcases p10064_3 (m.d 1 3) (by simp) with h10070 | h10070
                                          · rcases p10064_3 (m.d 1 4) (by simp) with h10071 | h10071
                                            · linarith only [h10071, hlam, p10064_0]
                                            · rcases p10064_3 (m.d 1 5) (by simp) with h10073 | h10073
                                              · linarith only [h10073, h9936, hlam]
                                              · linarith only [h10033, h10073, hlam]
                                          · linarith only [h10031, h10070, hlam]
                                        · linarith only [h10029, h10069, hlam]
                                      · linarith only [h10068, hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      rcases p10064_3 (m.d 0 1) (by simp) with h10079 | h10079
                                      · rcases p10064_3 (m.d 1 2) (by simp) with h10080 | h10080
                                        · rcases p10064_3 (m.d 1 3) (by simp) with h10081 | h10081
                                          · rcases p10064_3 (m.d 1 4) (by simp) with h10082 | h10082
                                            · linarith only [h10082, h9935, hlam]
                                            · rcases p10064_3 (m.d 1 5) (by simp) with h10084 | h10084
                                              · linarith only [h10084, hlam, p10064_0]
                                              · rcases h3bigk with h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c | h10086c
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h6310, hlam, p10086_1]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h10036, h10039, h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10086_1, u0elo1]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  rcases p10086_3 (m.d 0 3) (by simp) with h10090 | h10090
                                                  · rcases p10086_3 (m.d 1 3) (by simp) with h10091 | h10091
                                                    · rcases p10086_3 (m.d 2 3) (by simp) with h10092 | h10092
                                                      · linarith only [h10092, h9937, hlam]
                                                      · linarith only [h10035, h10092, hlam]
                                                    · linarith only [h10031, h10091, hlam]
                                                  · linarith only [h10090, hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  rcases p10086_3 (m.d 0 3) (by simp) with h10097 | h10097
                                                  · rcases p10086_3 (m.d 1 3) (by simp) with h10098 | h10098
                                                    · rcases p10086_3 (m.d 2 3) (by simp) with h10099 | h10099
                                                      · linarith only [h10099, h9937, hlam]
                                                      · linarith only [h10036, h10099, hlam]
                                                    · linarith only [h10032, h10098, hlam]
                                                  · linarith only [h10097, hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h10028, h10029, h10035, h6310, h9935, h9942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10086_1]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  rcases p10086_3 (m.d 0 3) (by simp) with h10106 | h10106
                                                  · linarith only [h10106, h6310, hlam]
                                                  · linarith only [h10106, h9937, hlam]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h10029, h10035, h6310, h9935, h9942, hlam, p10041_1, p10086_2]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h6310, h9941, hlam, p10041_1, p10086_2]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h9937, hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h10028, hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10086_1, u0elo1]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h9937, hc35, hlam, hphi, ht0b, ht5b, p10086_1, u0elo1]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h9940, hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h10031, hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h10035, hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h10039, hlam, p10086_1]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h9941, hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h10032, hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h10036, hlam, p10086_0]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [h9941, hc34, hlam, hphi, ht0b, ht45, ht5b, p10086_1, u0elo2]
                                                · have p10086_0 := h10086c.1
                                                  have p10086_1 := h10086c.2.1
                                                  have p10086_2 := h10086c.2.2.1
                                                  have p10086_3 := h10086c.2.2.2
                                                  linarith only [hlam, p10086_0]
                                          · linarith only [h10032, h10081, hlam]
                                        · linarith only [h10030, h10080, hlam]
                                      · linarith only [h10079, hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10029, h10035, h9935, h9942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10064_1]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10029, h10035, h6310, h9935, h9942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10064_1]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h0, h9935, h9942, hlam, p10041_1, p10064_2]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10028, h6310, h9936, hlam, p10041_1, p10064_2]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10028, h10029, h10035, h9935, h9942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10064_1]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10028, hlam, p10064_1]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h6310, h9935, h9942, hlam, p10041_1, p10064_2]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h6310, h9936, hlam, p10041_1, p10064_2]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h9935, hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10029, hlam, p10064_1]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10031, hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10033, hlam, p10064_1]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h9936, hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10030, hlam, p10064_1]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10032, hlam, p10064_0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [h10029, h10035, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10041_1, p10064_1, u0elo0]
                                    · have p10064_0 := h10064c.1
                                      have p10064_1 := h10064c.2.1
                                      have p10064_2 := h10064c.2.2.1
                                      have p10064_3 := h10064c.2.2.2
                                      linarith only [hlam, p10064_0]
                                  · rcases h1bigk with h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c | h10149c
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h0, hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h6310, hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      rcases p10149_3 (m.d 0 1) (by simp) with h10153 | h10153
                                      · rcases p10149_3 (m.d 1 2) (by simp) with h10154 | h10154
                                        · rcases p10149_3 (m.d 1 3) (by simp) with h10155 | h10155
                                          · rcases p10149_3 (m.d 1 4) (by simp) with h10156 | h10156
                                            · linarith only [h10156, hlam, p10149_0]
                                            · rcases p10149_3 (m.d 1 5) (by simp) with h10158 | h10158
                                              · linarith only [h10158, h9936, hlam]
                                              · linarith only [h10033, h10158, hlam]
                                          · linarith only [h10031, h10155, hlam]
                                        · linarith only [h10029, h10154, hlam]
                                      · linarith only [h10153, hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      rcases p10149_3 (m.d 0 1) (by simp) with h10164 | h10164
                                      · rcases p10149_3 (m.d 1 2) (by simp) with h10165 | h10165
                                        · rcases p10149_3 (m.d 1 3) (by simp) with h10166 | h10166
                                          · rcases p10149_3 (m.d 1 4) (by simp) with h10167 | h10167
                                            · linarith only [h10167, h9935, hlam]
                                            · rcases p10149_3 (m.d 1 5) (by simp) with h10169 | h10169
                                              · linarith only [h10169, hlam, p10149_0]
                                              · rcases h3bigk with h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c | h10171c
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h6310, hlam, p10171_1]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h10035, h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10171_1, u0elo1]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  rcases p10171_3 (m.d 0 3) (by simp) with h10175 | h10175
                                                  · rcases p10171_3 (m.d 1 3) (by simp) with h10176 | h10176
                                                    · rcases p10171_3 (m.d 2 3) (by simp) with h10177 | h10177
                                                      · linarith only [h10177, h9937, hlam]
                                                      · linarith only [h10035, h10177, hlam]
                                                    · linarith only [h10031, h10176, hlam]
                                                  · linarith only [h10175, hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  rcases p10171_3 (m.d 0 3) (by simp) with h10182 | h10182
                                                  · rcases p10171_3 (m.d 1 3) (by simp) with h10183 | h10183
                                                    · rcases p10171_3 (m.d 2 3) (by simp) with h10184 | h10184
                                                      · linarith only [h10184, h9937, hlam]
                                                      · linarith only [h10036, h10184, hlam]
                                                    · linarith only [h10032, h10183, hlam]
                                                  · linarith only [h10182, hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h10028, h6310, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10041_1, p10171_1]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  rcases p10171_3 (m.d 0 3) (by simp) with h10191 | h10191
                                                  · linarith only [h10191, h6310, hlam]
                                                  · linarith only [h10191, h9937, hlam]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h10029, h10035, h6310, h9935, h9942, hlam, p10041_1, p10171_2]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h10036, h6310, h9939, hlam, p10041_1, p10171_2]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h9937, hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h10028, hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10171_1, u0elo1]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h9937, hc35, hlam, hphi, ht0b, ht5b, p10171_1, u0elo1]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h9940, hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h10031, hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h10035, hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h10039, hlam, p10171_1]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h9941, hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h10032, hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h10036, hlam, p10171_0]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [h9941, hc34, hlam, hphi, ht0b, ht45, ht5b, p10171_1, u0elo2]
                                                · have p10171_0 := h10171c.1
                                                  have p10171_1 := h10171c.2.1
                                                  have p10171_2 := h10171c.2.2.1
                                                  have p10171_3 := h10171c.2.2.2
                                                  linarith only [hlam, p10171_0]
                                          · linarith only [h10032, h10166, hlam]
                                        · linarith only [h10030, h10165, hlam]
                                      · linarith only [h10164, hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10029, h10035, h9935, h9942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10149_1]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10029, h10035, h6310, h9935, h9942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10149_1]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h0, h9935, h9942, hlam, p10041_1, p10149_2]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10028, h6310, h9936, hlam, p10041_1, p10149_2]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10028, h10029, h10035, h9935, h9942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10149_1]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10028, hlam, p10149_1]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h6310, h9935, h9942, hlam, p10041_1, p10149_2]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h6310, h9936, hlam, p10041_1, p10149_2]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h9935, hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10029, hlam, p10149_1]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10031, hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10033, hlam, p10149_1]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h9936, hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10030, hlam, p10149_1]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10032, hlam, p10149_0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [h10029, h10035, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10041_1, p10149_1, u0elo0]
                                    · have p10149_0 := h10149c.1
                                      have p10149_1 := h10149c.2.1
                                      have p10149_2 := h10149c.2.2.1
                                      have p10149_3 := h10149c.2.2.2
                                      linarith only [hlam, p10149_0]
                                  · rcases h1bigk with h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h0, hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h6310, hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      rcases p10234_3 (m.d 0 1) (by simp) with h10238 | h10238
                                      · rcases p10234_3 (m.d 1 2) (by simp) with h10239 | h10239
                                        · rcases p10234_3 (m.d 1 3) (by simp) with h10240 | h10240
                                          · rcases p10234_3 (m.d 1 4) (by simp) with h10241 | h10241
                                            · linarith only [h10241, hlam, p10234_0]
                                            · rcases p10234_3 (m.d 1 5) (by simp) with h10243 | h10243
                                              · linarith only [h10243, h9936, hlam]
                                              · linarith only [h10033, h10243, hlam]
                                          · linarith only [h10031, h10240, hlam]
                                        · linarith only [h10029, h10239, hlam]
                                      · linarith only [h10238, hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      rcases p10234_3 (m.d 0 1) (by simp) with h10249 | h10249
                                      · rcases p10234_3 (m.d 1 2) (by simp) with h10250 | h10250
                                        · rcases p10234_3 (m.d 1 3) (by simp) with h10251 | h10251
                                          · rcases p10234_3 (m.d 1 4) (by simp) with h10252 | h10252
                                            · linarith only [h10252, h9935, hlam]
                                            · rcases p10234_3 (m.d 1 5) (by simp) with h10254 | h10254
                                              · linarith only [h10254, hlam, p10234_0]
                                              · rcases h3bigk with h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c | h10256c
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h6310, hlam, p10256_1]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h10035, h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10256_1, u0elo1]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  rcases p10256_3 (m.d 0 3) (by simp) with h10260 | h10260
                                                  · rcases p10256_3 (m.d 1 3) (by simp) with h10261 | h10261
                                                    · rcases p10256_3 (m.d 2 3) (by simp) with h10262 | h10262
                                                      · linarith only [h10262, h9937, hlam]
                                                      · linarith only [h10035, h10262, hlam]
                                                    · linarith only [h10031, h10261, hlam]
                                                  · linarith only [h10260, hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  rcases p10256_3 (m.d 0 3) (by simp) with h10267 | h10267
                                                  · rcases p10256_3 (m.d 1 3) (by simp) with h10268 | h10268
                                                    · rcases p10256_3 (m.d 2 3) (by simp) with h10269 | h10269
                                                      · linarith only [h10269, h9937, hlam]
                                                      · linarith only [h10036, h10269, hlam]
                                                    · linarith only [h10032, h10268, hlam]
                                                  · linarith only [h10267, hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h10028, h10063, hc12, hlam, ht01, p10256_1]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  rcases p10256_3 (m.d 0 3) (by simp) with h10276 | h10276
                                                  · linarith only [h10276, h6310, hlam]
                                                  · linarith only [h10276, h9937, hlam]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h10029, h10035, h6310, h9935, h9942, hlam, p10041_1, p10256_2]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h6310, h9941, hlam, p10041_1, p10256_2]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h9937, hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h10028, hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10256_1, u0elo1]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h9937, hc35, hlam, hphi, ht0b, ht5b, p10256_1, u0elo1]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h9940, hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h10031, hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h10035, hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h10039, hlam, p10256_1]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h9941, hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h10032, hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h10036, hlam, p10256_0]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [h9941, hc34, hlam, hphi, ht0b, ht45, ht5b, p10256_1, u0elo2]
                                                · have p10256_0 := h10256c.1
                                                  have p10256_1 := h10256c.2.1
                                                  have p10256_2 := h10256c.2.2.1
                                                  have p10256_3 := h10256c.2.2.2
                                                  linarith only [hlam, p10256_0]
                                          · linarith only [h10032, h10251, hlam]
                                        · linarith only [h10030, h10250, hlam]
                                      · linarith only [h10249, hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10029, h10035, h9935, h9942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10234_1]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10029, h10035, h6310, h9935, h9942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10234_1]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h0, h9935, h9942, hlam, p10041_1, p10234_2]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10028, h6310, h9936, hlam, p10041_1, p10234_2]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10028, h10029, h10035, h9935, h9942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10234_1]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10028, hlam, p10234_1]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h6310, h9935, h9942, hlam, p10041_1, p10234_2]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h6310, h9936, hlam, p10041_1, p10234_2]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h9935, hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10029, hlam, p10234_1]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10031, hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10033, hlam, p10234_1]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h9936, hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10030, hlam, p10234_1]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10032, hlam, p10234_0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [h10029, h10035, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10041_1, p10234_1, u0elo0]
                                    · have p10234_0 := h10234c.1
                                      have p10234_1 := h10234c.2.1
                                      have p10234_2 := h10234c.2.2.1
                                      have p10234_3 := h10234c.2.2.2
                                      linarith only [hlam, p10234_0]
                                  · linarith only [h10063, h6310, h9937, h9942, hlam, p10041_1, u0elo1]
                                  · linarith only [h10063, h6310, h9937, hlam, p10041_1, u0elo1]
                            · linarith only [h10058, h9941, hlam]
                          · linarith only [h10057, h9939, hlam]
                        · linarith only [h10056, h9936, hlam]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h10029, h10035, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10041_1, u0elo1]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h10029, h10035, h6310, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10041_1, u0elo1]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        rcases p10041_3 (m.d 0 1) (by simp) with h10327 | h10327
                        · linarith only [h0, h10327, hlam]
                        · linarith only [h10327, h9935, hlam]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        rcases p10041_3 (m.d 0 1) (by simp) with h10330 | h10330
                        · linarith only [h0, h10330, hlam]
                        · linarith only [h10330, h9936, hlam]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h10030, h10035, h10037, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10041_1, u0elo2]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h9937, hlam, p10041_1]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        rcases p10041_3 (m.d 0 1) (by simp) with h10336 | h10336
                        · linarith only [h10336, h6310, hlam]
                        · linarith only [h10336, h9935, hlam]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        rcases p10041_3 (m.d 0 1) (by simp) with h10339 | h10339
                        · linarith only [h10339, h6310, hlam]
                        · linarith only [h10339, h9936, hlam]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h9935, hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h9938, hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h9940, hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h9942, hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h9936, hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h9939, hlam, p10041_1]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [h9941, hlam, p10041_0]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        rcases p10041_3 (m.d 0 1) (by simp) with h10350 | h10350
                        · rcases p10041_3 (m.d 0 2) (by simp) with h10351 | h10351
                          · rcases p10041_3 (m.d 0 3) (by simp) with h10352 | h10352
                            · rcases p10041_3 (m.d 0 4) (by simp) with h10353 | h10353
                              · linarith only [h10353, h9942, hlam]
                              · rcases p10041_3 (m.d 0 5) (by simp) with h10355 | h10355
                                · rcases h0emin with h10356 | h10356 | h10356 | h10356 | h10356
                                  · rcases h1bigk with h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c | h10357c
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h0, hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h6310, hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      rcases p10357_3 (m.d 0 1) (by simp) with h10361 | h10361
                                      · rcases p10357_3 (m.d 1 2) (by simp) with h10362 | h10362
                                        · rcases p10357_3 (m.d 1 3) (by simp) with h10363 | h10363
                                          · rcases p10357_3 (m.d 1 4) (by simp) with h10364 | h10364
                                            · linarith only [h10364, hlam, p10357_0]
                                            · rcases p10357_3 (m.d 1 5) (by simp) with h10366 | h10366
                                              · linarith only [h10366, h9936, hlam]
                                              · linarith only [h10033, h10366, hlam]
                                          · linarith only [h10031, h10363, hlam]
                                        · linarith only [h10029, h10362, hlam]
                                      · linarith only [h10361, hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      rcases p10357_3 (m.d 0 1) (by simp) with h10372 | h10372
                                      · rcases p10357_3 (m.d 1 2) (by simp) with h10373 | h10373
                                        · rcases p10357_3 (m.d 1 3) (by simp) with h10374 | h10374
                                          · rcases p10357_3 (m.d 1 4) (by simp) with h10375 | h10375
                                            · linarith only [h10375, h9935, hlam]
                                            · rcases p10357_3 (m.d 1 5) (by simp) with h10377 | h10377
                                              · linarith only [h10377, hlam, p10357_0]
                                              · rcases h3bigk with h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c | h10379c
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h6310, hlam, p10379_1]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h10035, h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10379_1, u0elo1]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  rcases p10379_3 (m.d 0 3) (by simp) with h10383 | h10383
                                                  · rcases p10379_3 (m.d 1 3) (by simp) with h10384 | h10384
                                                    · rcases p10379_3 (m.d 2 3) (by simp) with h10385 | h10385
                                                      · linarith only [h10385, h9937, hlam]
                                                      · linarith only [h10035, h10385, hlam]
                                                    · linarith only [h10031, h10384, hlam]
                                                  · linarith only [h10383, hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  rcases p10379_3 (m.d 0 3) (by simp) with h10390 | h10390
                                                  · rcases p10379_3 (m.d 1 3) (by simp) with h10391 | h10391
                                                    · rcases p10379_3 (m.d 2 3) (by simp) with h10392 | h10392
                                                      · linarith only [h10392, h9937, hlam]
                                                      · linarith only [h10036, h10392, hlam]
                                                    · linarith only [h10032, h10391, hlam]
                                                  · linarith only [h10390, hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h10028, h10029, h10035, h6310, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10379_1]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  rcases p10379_3 (m.d 0 3) (by simp) with h10399 | h10399
                                                  · linarith only [h10399, h6310, hlam]
                                                  · linarith only [h10399, h9937, hlam]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h10029, h10035, h6310, h9935, h9936, hlam, p10041_1, p10379_2]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h10032, h6310, hlam, p10357_1, p10379_2]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h9937, hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h10028, hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10379_1, u0elo1]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h9937, hc35, hlam, hphi, ht0b, ht5b, p10379_1, u0elo1]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h9940, hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h10031, hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h10035, hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h10039, hlam, p10379_1]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h9941, hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h10032, hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h10036, hlam, p10379_0]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [h9941, hc34, hlam, hphi, ht0b, ht45, ht5b, p10379_1, u0elo2]
                                                · have p10379_0 := h10379c.1
                                                  have p10379_1 := h10379c.2.1
                                                  have p10379_2 := h10379c.2.2.1
                                                  have p10379_3 := h10379c.2.2.2
                                                  linarith only [hlam, p10379_0]
                                          · linarith only [h10032, h10374, hlam]
                                        · linarith only [h10030, h10373, hlam]
                                      · linarith only [h10372, hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h10029, h10035, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10357_1]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h10029, h10035, h6310, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10357_1]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h0, h9935, h9936, hlam, p10041_1, p10357_2]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      rcases p10357_3 (m.d 0 1) (by simp) with h10426 | h10426
                                      · linarith only [h0, h10426, hlam]
                                      · linarith only [h10426, h9936, hlam]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h10028, h10029, h10035, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10357_1]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h10028, hlam, p10357_1]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h6310, h9935, h9936, hlam, p10041_1, p10357_2]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      rcases p10357_3 (m.d 0 1) (by simp) with h10433 | h10433
                                      · linarith only [h10433, h6310, hlam]
                                      · linarith only [h10433, h9936, hlam]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h9935, hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h10029, hlam, p10357_1]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h10031, hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h10033, hlam, p10357_1]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h9936, hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h10030, hlam, p10357_1]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h10032, hlam, p10357_0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [h10029, h10035, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10357_1, u0elo0]
                                    · have p10357_0 := h10357c.1
                                      have p10357_1 := h10357c.2.1
                                      have p10357_2 := h10357c.2.2.1
                                      have p10357_3 := h10357c.2.2.2
                                      linarith only [hlam, p10357_0]
                                  · rcases h1bigk with h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c | h10446c
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h0, hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h6310, hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      rcases p10446_3 (m.d 0 1) (by simp) with h10450 | h10450
                                      · rcases p10446_3 (m.d 1 2) (by simp) with h10451 | h10451
                                        · rcases p10446_3 (m.d 1 3) (by simp) with h10452 | h10452
                                          · rcases p10446_3 (m.d 1 4) (by simp) with h10453 | h10453
                                            · linarith only [h10453, hlam, p10446_0]
                                            · rcases p10446_3 (m.d 1 5) (by simp) with h10455 | h10455
                                              · linarith only [h10455, h9936, hlam]
                                              · linarith only [h10033, h10455, hlam]
                                          · linarith only [h10031, h10452, hlam]
                                        · linarith only [h10029, h10451, hlam]
                                      · linarith only [h10450, hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      rcases p10446_3 (m.d 0 1) (by simp) with h10461 | h10461
                                      · rcases p10446_3 (m.d 1 2) (by simp) with h10462 | h10462
                                        · rcases p10446_3 (m.d 1 3) (by simp) with h10463 | h10463
                                          · rcases p10446_3 (m.d 1 4) (by simp) with h10464 | h10464
                                            · linarith only [h10464, h9935, hlam]
                                            · rcases p10446_3 (m.d 1 5) (by simp) with h10466 | h10466
                                              · linarith only [h10466, hlam, p10446_0]
                                              · rcases h3bigk with h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c | h10468c
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h6310, hlam, p10468_1]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h10035, h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10468_1, u0elo1]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  rcases p10468_3 (m.d 0 3) (by simp) with h10472 | h10472
                                                  · rcases p10468_3 (m.d 1 3) (by simp) with h10473 | h10473
                                                    · rcases p10468_3 (m.d 2 3) (by simp) with h10474 | h10474
                                                      · linarith only [h10474, h9937, hlam]
                                                      · linarith only [h10035, h10474, hlam]
                                                    · linarith only [h10031, h10473, hlam]
                                                  · linarith only [h10472, hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  rcases p10468_3 (m.d 0 3) (by simp) with h10479 | h10479
                                                  · rcases p10468_3 (m.d 1 3) (by simp) with h10480 | h10480
                                                    · rcases p10468_3 (m.d 2 3) (by simp) with h10481 | h10481
                                                      · linarith only [h10481, h9937, hlam]
                                                      · linarith only [h10036, h10481, hlam]
                                                    · linarith only [h10032, h10480, hlam]
                                                  · linarith only [h10479, hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h10028, h6310, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p10446_1, p10468_1]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  rcases p10468_3 (m.d 0 3) (by simp) with h10488 | h10488
                                                  · linarith only [h10488, h6310, hlam]
                                                  · linarith only [h10488, h9937, hlam]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h10029, h10035, h6310, h9935, h9936, hlam, p10041_1, p10468_2]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h10032, h6310, hlam, p10446_1, p10468_2]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h9937, hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h10028, hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10468_1, u0elo1]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h9937, hc35, hlam, hphi, ht0b, ht5b, p10468_1, u0elo1]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h9940, hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h10031, hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h10035, hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h10039, hlam, p10468_1]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h9941, hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h10032, hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h10036, hlam, p10468_0]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [h9941, hc34, hlam, hphi, ht0b, ht45, ht5b, p10468_1, u0elo2]
                                                · have p10468_0 := h10468c.1
                                                  have p10468_1 := h10468c.2.1
                                                  have p10468_2 := h10468c.2.2.1
                                                  have p10468_3 := h10468c.2.2.2
                                                  linarith only [hlam, p10468_0]
                                          · linarith only [h10032, h10463, hlam]
                                        · linarith only [h10030, h10462, hlam]
                                      · linarith only [h10461, hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h10029, h10035, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10446_1]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h10029, h10035, h6310, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10446_1]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h0, h9935, h9936, hlam, p10041_1, p10446_2]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      rcases p10446_3 (m.d 0 1) (by simp) with h10515 | h10515
                                      · linarith only [h0, h10515, hlam]
                                      · linarith only [h10515, h9936, hlam]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h10028, h10029, h10035, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10446_1]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h10028, hlam, p10446_1]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h6310, h9935, h9936, hlam, p10041_1, p10446_2]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      rcases p10446_3 (m.d 0 1) (by simp) with h10522 | h10522
                                      · linarith only [h10522, h6310, hlam]
                                      · linarith only [h10522, h9936, hlam]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h9935, hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h10029, hlam, p10446_1]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h10031, hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h10033, hlam, p10446_1]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h9936, hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h10030, hlam, p10446_1]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h10032, hlam, p10446_0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [h10029, h10035, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10446_1, u0elo0]
                                    · have p10446_0 := h10446c.1
                                      have p10446_1 := h10446c.2.1
                                      have p10446_2 := h10446c.2.2.1
                                      have p10446_3 := h10446c.2.2.2
                                      linarith only [hlam, p10446_0]
                                  · rcases h1bigk with h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c | h10535c
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h0, hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h6310, hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      rcases p10535_3 (m.d 0 1) (by simp) with h10539 | h10539
                                      · rcases p10535_3 (m.d 1 2) (by simp) with h10540 | h10540
                                        · rcases p10535_3 (m.d 1 3) (by simp) with h10541 | h10541
                                          · rcases p10535_3 (m.d 1 4) (by simp) with h10542 | h10542
                                            · linarith only [h10542, hlam, p10535_0]
                                            · rcases p10535_3 (m.d 1 5) (by simp) with h10544 | h10544
                                              · linarith only [h10544, h9936, hlam]
                                              · linarith only [h10033, h10544, hlam]
                                          · linarith only [h10031, h10541, hlam]
                                        · linarith only [h10029, h10540, hlam]
                                      · linarith only [h10539, hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      rcases p10535_3 (m.d 0 1) (by simp) with h10550 | h10550
                                      · rcases p10535_3 (m.d 1 2) (by simp) with h10551 | h10551
                                        · rcases p10535_3 (m.d 1 3) (by simp) with h10552 | h10552
                                          · rcases p10535_3 (m.d 1 4) (by simp) with h10553 | h10553
                                            · linarith only [h10553, h9935, hlam]
                                            · rcases p10535_3 (m.d 1 5) (by simp) with h10555 | h10555
                                              · linarith only [h10555, hlam, p10535_0]
                                              · rcases h3bigk with h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c | h10557c
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h6310, hlam, p10557_1]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h10035, h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10557_1, u0elo1]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  rcases p10557_3 (m.d 0 3) (by simp) with h10561 | h10561
                                                  · rcases p10557_3 (m.d 1 3) (by simp) with h10562 | h10562
                                                    · rcases p10557_3 (m.d 2 3) (by simp) with h10563 | h10563
                                                      · linarith only [h10563, h9937, hlam]
                                                      · linarith only [h10035, h10563, hlam]
                                                    · linarith only [h10031, h10562, hlam]
                                                  · linarith only [h10561, hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  rcases p10557_3 (m.d 0 3) (by simp) with h10568 | h10568
                                                  · rcases p10557_3 (m.d 1 3) (by simp) with h10569 | h10569
                                                    · rcases p10557_3 (m.d 2 3) (by simp) with h10570 | h10570
                                                      · linarith only [h10570, h9937, hlam]
                                                      · linarith only [h10036, h10570, hlam]
                                                    · linarith only [h10032, h10569, hlam]
                                                  · linarith only [h10568, hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h10028, h10356, hc12, hlam, ht01, p10557_1]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  rcases p10557_3 (m.d 0 3) (by simp) with h10577 | h10577
                                                  · linarith only [h10577, h6310, hlam]
                                                  · linarith only [h10577, h9937, hlam]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h10029, h10035, h6310, h9935, h9936, hlam, p10041_1, p10557_2]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h10032, h6310, hlam, p10535_1, p10557_2]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h9937, hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h10028, hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10557_1, u0elo1]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h9937, hc35, hlam, hphi, ht0b, ht5b, p10557_1, u0elo1]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h9940, hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h10031, hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h10035, hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h10039, hlam, p10557_1]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h9941, hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h10032, hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h10036, hlam, p10557_0]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [h9941, hc34, hlam, hphi, ht0b, ht45, ht5b, p10557_1, u0elo2]
                                                · have p10557_0 := h10557c.1
                                                  have p10557_1 := h10557c.2.1
                                                  have p10557_2 := h10557c.2.2.1
                                                  have p10557_3 := h10557c.2.2.2
                                                  linarith only [hlam, p10557_0]
                                          · linarith only [h10032, h10552, hlam]
                                        · linarith only [h10030, h10551, hlam]
                                      · linarith only [h10550, hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h10029, h10035, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10535_1]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h10029, h10035, h6310, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10535_1]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h0, h9935, h9936, hlam, p10041_1, p10535_2]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      rcases p10535_3 (m.d 0 1) (by simp) with h10604 | h10604
                                      · linarith only [h0, h10604, hlam]
                                      · linarith only [h10604, h9936, hlam]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h10028, h10029, h10035, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10535_1]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h10028, hlam, p10535_1]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h6310, h9935, h9936, hlam, p10041_1, p10535_2]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      rcases p10535_3 (m.d 0 1) (by simp) with h10611 | h10611
                                      · linarith only [h10611, h6310, hlam]
                                      · linarith only [h10611, h9936, hlam]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h9935, hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h10029, hlam, p10535_1]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h10031, hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h10033, hlam, p10535_1]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h9936, hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h10030, hlam, p10535_1]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h10032, hlam, p10535_0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [h10029, h10035, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10535_1, u0elo0]
                                    · have p10535_0 := h10535c.1
                                      have p10535_1 := h10535c.2.1
                                      have p10535_2 := h10535c.2.2.1
                                      have p10535_3 := h10535c.2.2.2
                                      linarith only [hlam, p10535_0]
                                  · linarith only [h10356, hlam, p10041_1, u0elo4]
                                  · rcases h1bigk with h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c | h10625c
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h0, hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h6310, hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      rcases p10625_3 (m.d 0 1) (by simp) with h10629 | h10629
                                      · rcases p10625_3 (m.d 1 2) (by simp) with h10630 | h10630
                                        · rcases p10625_3 (m.d 1 3) (by simp) with h10631 | h10631
                                          · rcases p10625_3 (m.d 1 4) (by simp) with h10632 | h10632
                                            · linarith only [h10632, hlam, p10625_0]
                                            · rcases p10625_3 (m.d 1 5) (by simp) with h10634 | h10634
                                              · linarith only [h10634, h9936, hlam]
                                              · linarith only [h10033, h10634, hlam]
                                          · linarith only [h10031, h10631, hlam]
                                        · linarith only [h10029, h10630, hlam]
                                      · linarith only [h10629, hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      rcases p10625_3 (m.d 0 1) (by simp) with h10640 | h10640
                                      · rcases p10625_3 (m.d 1 2) (by simp) with h10641 | h10641
                                        · rcases p10625_3 (m.d 1 3) (by simp) with h10642 | h10642
                                          · rcases p10625_3 (m.d 1 4) (by simp) with h10643 | h10643
                                            · linarith only [h10643, h9935, hlam]
                                            · rcases p10625_3 (m.d 1 5) (by simp) with h10645 | h10645
                                              · linarith only [h10645, hlam, p10625_0]
                                              · rcases h3bigk with h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h6310, hlam, p10647_1]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h10035, h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10647_1, u0elo1]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  rcases p10647_3 (m.d 0 3) (by simp) with h10651 | h10651
                                                  · rcases p10647_3 (m.d 1 3) (by simp) with h10652 | h10652
                                                    · rcases p10647_3 (m.d 2 3) (by simp) with h10653 | h10653
                                                      · linarith only [h10653, h9937, hlam]
                                                      · linarith only [h10035, h10653, hlam]
                                                    · linarith only [h10031, h10652, hlam]
                                                  · linarith only [h10651, hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  rcases p10647_3 (m.d 0 3) (by simp) with h10658 | h10658
                                                  · rcases p10647_3 (m.d 1 3) (by simp) with h10659 | h10659
                                                    · rcases p10647_3 (m.d 2 3) (by simp) with h10660 | h10660
                                                      · linarith only [h10660, h9937, hlam]
                                                      · linarith only [h10036, h10660, hlam]
                                                    · linarith only [h10032, h10659, hlam]
                                                  · linarith only [h10658, hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h10028, h6310, h9936, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10647_1]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  rcases p10647_3 (m.d 0 3) (by simp) with h10667 | h10667
                                                  · linarith only [h10667, h6310, hlam]
                                                  · linarith only [h10667, h9937, hlam]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h10029, h10035, h6310, h9935, h9936, hlam, p10041_1, p10647_2]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h10032, h6310, hlam, p10625_1, p10647_2]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h9937, hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h10028, hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, p10647_1, u0elo1]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h9937, hc35, hlam, hphi, ht0b, ht5b, p10647_1, u0elo1]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h9940, hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h10031, hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h10035, hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h10039, hlam, p10647_1]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h9941, hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h10032, hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h10036, hlam, p10647_0]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [h9941, hc34, hlam, hphi, ht0b, ht45, ht5b, p10647_1, u0elo2]
                                                · have p10647_0 := h10647c.1
                                                  have p10647_1 := h10647c.2.1
                                                  have p10647_2 := h10647c.2.2.1
                                                  have p10647_3 := h10647c.2.2.2
                                                  linarith only [hlam, p10647_0]
                                          · linarith only [h10032, h10642, hlam]
                                        · linarith only [h10030, h10641, hlam]
                                      · linarith only [h10640, hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h10029, h10035, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10625_1]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h10029, h10035, h6310, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10625_1]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h0, h9935, h9936, hlam, p10041_1, p10625_2]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      rcases p10625_3 (m.d 0 1) (by simp) with h10694 | h10694
                                      · linarith only [h0, h10694, hlam]
                                      · linarith only [h10694, h9936, hlam]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h10028, h10029, h10035, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10041_1, p10625_1]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h10028, hlam, p10625_1]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h6310, h9935, h9936, hlam, p10041_1, p10625_2]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      rcases p10625_3 (m.d 0 1) (by simp) with h10701 | h10701
                                      · linarith only [h10701, h6310, hlam]
                                      · linarith only [h10701, h9936, hlam]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h9935, hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h10029, hlam, p10625_1]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h10031, hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h10033, hlam, p10625_1]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h9936, hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h10030, hlam, p10625_1]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h10032, hlam, p10625_0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [h10029, h10035, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10625_1, u0elo0]
                                    · have p10625_0 := h10625c.1
                                      have p10625_1 := h10625c.2.1
                                      have p10625_2 := h10625c.2.2.1
                                      have p10625_3 := h10625c.2.2.2
                                      linarith only [hlam, p10625_0]
                                · linarith only [h10355, h9942, hlam]
                            · linarith only [h10352, h9940, hlam]
                          · linarith only [h10351, h9938, hlam]
                        · linarith only [h10350, h9935, hlam]
                      · have p10041_0 := h10041c.1
                        have p10041_1 := h10041c.2.1
                        have p10041_2 := h10041c.2.2.1
                        have p10041_3 := h10041c.2.2.2
                        linarith only [hlam, p10041_0]
                · linarith only [h10032, h10035, h10036, h6310, h9936, h9937, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h10720 | h10720
                · linarith only [h10035, h10720, h9937, h9940, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h10722 | h10722
                  · linarith only [h10031, h10035, h10722, h9935, h9942, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10724 | h10724
                    · linarith only [h10031, h10724, h9935, h9942, hlam]
                    · rcases h0bigk with h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c | h10726c
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h0, hlam, p10726_1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h6310, hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h10031, h10035, h6310, h9935, h9937, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10726_1, u0elo1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h10035, h10724, h6310, h9937, h9941, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10726_1, u0elo1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h10031, h10035, h9935, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10726_1, u0elo1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h10031, h10035, h6310, h9935, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10726_1, u0elo1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h10031, h10035, h9935, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10726_1, u0elo1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h10035, h10724, h9941, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10726_1, u0elo1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h10031, h10035, h9935, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10726_1, u0elo2]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h9937, hlam, p10726_1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h10031, h10035, h9935, h9937, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10726_1, u0elo1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h10035, h10724, h9937, h9941, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10726_1, u0elo1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h9935, hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h9938, hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h9940, hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h9942, hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h9936, hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h9939, hlam, p10726_1]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h9941, hlam, p10726_0]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [h10031, h10035, h9935, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10726_1, u0elo4]
                      · have p10726_0 := h10726c.1
                        have p10726_1 := h10726c.2.1
                        have p10726_2 := h10726c.2.2.1
                        have p10726_3 := h10726c.2.2.2
                        linarith only [hlam, p10726_0]
          · linarith only [h10032, h6310, h9941, hlam]
        · linarith only [h10031, h6310, h9940, hlam]
      · linarith only [h0, h10030, h9939, hlam]
    · linarith only [h0, h10029, h9938, hlam]
  · linarith only [h0, h10028, h9937, hlam]

end R2N4
