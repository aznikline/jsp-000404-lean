import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S9
import Jsp000404.R1LeavesN7_36S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x1_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1845 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2109 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3015 | h3015
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3016 | h3016
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3017 | h3017
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3018 | h3018
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3019 | h3019
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3020 | h3020
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3021 | h3021
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3022 | h3022
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3023 | h3023
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3024 | h3024
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3025 | h3025
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3026 | h3026
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3027 | h3027
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3028 | h3028
                            · rcases h3bigk with h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h1845, hlam, p3029_1]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3025, h3028, hc03, hc45, hlam, hphi, ht0b, ht5b, p3029_1]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                rcases p3029_3 (m.d 0 3) (by simp) with h3033 | h3033
                                · rcases p3029_3 (m.d 1 3) (by simp) with h3034 | h3034
                                  · rcases p3029_3 (m.d 2 3) (by simp) with h3035 | h3035
                                    · linarith only [h3015, h3035, hlam]
                                    · linarith only [h3025, h3035, hlam]
                                  · linarith only [h3022, h3034, hlam]
                                · linarith only [h3033, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                rcases p3029_3 (m.d 0 3) (by simp) with h3040 | h3040
                                · rcases p3029_3 (m.d 1 3) (by simp) with h3041 | h3041
                                  · rcases p3029_3 (m.d 2 3) (by simp) with h3042 | h3042
                                    · linarith only [h3015, h3042, hlam]
                                    · linarith only [h3026, h3042, hlam]
                                  · linarith only [h3023, h3041, hlam]
                                · linarith only [h3040, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3015, h3025, h3028, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p3029_1]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3020, h3025, h3028, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3029_1]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                rcases p3029_3 (m.d 0 3) (by simp) with h3050 | h3050
                                · linarith only [h1845, h3050, hlam]
                                · linarith only [h3017, h3050, hlam]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                rcases p3029_3 (m.d 0 3) (by simp) with h3053 | h3053
                                · linarith only [h1845, h3053, hlam]
                                · linarith only [h3018, h3053, hlam]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3015, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3020, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3015, h3028, hc02, hc45, hlam, hphi, ht0b, ht5b, p3029_1]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                rcases p3029_3 (m.d 0 3) (by simp) with h3060 | h3060
                                · rcases p3029_3 (m.d 1 3) (by simp) with h3061 | h3061
                                  · rcases p3029_3 (m.d 2 3) (by simp) with h3062 | h3062
                                    · rcases p3029_3 (m.d 3 4) (by simp) with h3063 | h3063
                                      · linarith only [h3025, h3063, hlam]
                                      · linarith only [h3028, h3063, hlam]
                                    · linarith only [h3062, hlam, p3029_0]
                                  · linarith only [h3023, h3061, hlam]
                                · linarith only [h3018, h3060, hlam]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3017, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3022, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3025, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h0, h3015, h3025, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3029_1]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3018, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3023, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3026, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [h3028, hlam, p3029_0]
                              · have p3029_0 := h3029c.1
                                have p3029_1 := h3029c.2.1
                                have p3029_2 := h3029c.2.2.1
                                have p3029_3 := h3029c.2.2.2
                                linarith only [hlam, p3029_0]
                            · linarith only [h3019, h3028, hc34, hlam, hphi, u4elo0]
                          · linarith only [h2109, h3019, h3027, hc24, hlam, hphi, u4elo1]
                        · linarith only [h2109, h3018, h3019, h3025, h3026, hc34, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3082 | h3082
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3083 | h3083
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3084 | h3084
                            · rcases h3bigk with h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c | h3085c
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h1845, hlam, p3085_1]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                rcases p3085_3 (m.d 0 3) (by simp) with h3088 | h3088
                                · rcases p3085_3 (m.d 1 3) (by simp) with h3089 | h3089
                                  · rcases p3085_3 (m.d 2 3) (by simp) with h3090 | h3090
                                    · linarith only [h3015, h3090, hlam]
                                    · rcases p3085_3 (m.d 3 4) (by simp) with h3092 | h3092
                                      · linarith only [h3017, h3092, hlam]
                                      · linarith only [h3025, h3092, hlam]
                                  · linarith only [h3020, h3089, hlam]
                                · linarith only [h3015, h3088, hlam]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h1845, h3020, h3025, h3082, h3084, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3085_1]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3017, h3025, h3082, hlam, p3085_2]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3017, h3020, h3025, h3082, h3084, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3085_1]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                rcases p3085_3 (m.d 0 3) (by simp) with h3101 | h3101
                                · linarith only [h1845, h3101, hlam]
                                · linarith only [h3015, h3101, hlam]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3020, h3025, h3082, h3084, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3085_1]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h1845, h3017, h3025, h3082, hlam, p3085_2]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3015, hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3020, hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3025, hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3017, h3025, h3084, hc03, hc45, hlam, hphi, ht0b, ht5b, p3085_1]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3017, hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3022, hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, p3085_1, u4elo3]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                rcases p3085_3 (m.d 0 3) (by simp) with h3115 | h3115
                                · rcases p3085_3 (m.d 1 3) (by simp) with h3116 | h3116
                                  · rcases p3085_3 (m.d 2 3) (by simp) with h3117 | h3117
                                    · linarith only [h3025, h3117, hlam]
                                    · linarith only [h3082, h3117, hlam]
                                  · linarith only [h3023, h3116, hlam]
                                · linarith only [h3018, h3115, hlam]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3018, hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3023, hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3082, hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [h3084, hlam, p3085_0]
                              · have p3085_0 := h3085c.1
                                have p3085_1 := h3085c.2.1
                                have p3085_2 := h3085c.2.2.1
                                have p3085_3 := h3085c.2.2.2
                                linarith only [hlam, p3085_0]
                            · linarith only [h2109, h3019, h3084, hc34, hlam, hphi, u4elo1]
                          · linarith only [h2109, h3019, h3083, hc24, hlam, hphi, u4elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3129 | h3129
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3130 | h3130
                            · rcases h3bigk with h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h1845, hlam, p3131_1]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                rcases p3131_3 (m.d 0 3) (by simp) with h3134 | h3134
                                · rcases p3131_3 (m.d 1 3) (by simp) with h3135 | h3135
                                  · rcases p3131_3 (m.d 2 3) (by simp) with h3136 | h3136
                                    · linarith only [h3015, h3136, hlam]
                                    · rcases p3131_3 (m.d 3 4) (by simp) with h3138 | h3138
                                      · linarith only [h3017, h3138, hlam]
                                      · linarith only [h3025, h3138, hlam]
                                  · linarith only [h3020, h3135, hlam]
                                · linarith only [h3015, h3134, hlam]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                rcases p3131_3 (m.d 0 3) (by simp) with h3143 | h3143
                                · rcases p3131_3 (m.d 1 3) (by simp) with h3144 | h3144
                                  · rcases p3131_3 (m.d 2 3) (by simp) with h3145 | h3145
                                    · linarith only [h3015, h3145, hlam]
                                    · rcases p3131_3 (m.d 3 4) (by simp) with h3147 | h3147
                                      · linarith only [h3147, hlam, p3131_0]
                                      · rcases p3131_3 (m.d 3 5) (by simp) with h3149 | h3149
                                        · linarith only [h3018, h3149, hlam]
                                        · rcases h3emin with h3151 | h3151 | h3151 | h3151 | h3151
                                          · rcases h4bigk with h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h2109, hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h0, h2109, h3015, h3082, h3129, h3130, hc12, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p3131_1, p3152_1, u4elo1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h2109, h3082, h3130, hc23, hlam, hphi, ht34, p3152_1, u4elo1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              rcases p3152_3 (m.d 0 4) (by simp) with h3157 | h3157
                                              · rcases p3152_3 (m.d 1 4) (by simp) with h3158 | h3158
                                                · rcases p3152_3 (m.d 2 4) (by simp) with h3159 | h3159
                                                  · linarith only [h3016, h3159, hlam]
                                                  · linarith only [h3129, h3159, hlam]
                                                · linarith only [h3024, h3158, hlam]
                                              · linarith only [h3157, hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [hc04, hlam, hphi, p3152_1, u4elo1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h0, h3015, h3082, h3129, h3130, hc12, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p3131_1, p3152_1, u4elo1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h3082, h3130, hc23, hlam, hphi, ht34, p3152_1, u4elo1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              rcases p3152_3 (m.d 0 4) (by simp) with h3168 | h3168
                                              · linarith only [h2109, h3168, hlam]
                                              · linarith only [h3019, h3168, hlam]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h3016, hlam, p3152_1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h3021, hlam, p3152_1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h3025, hlam, p3152_1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h0, h3015, h3025, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3131_1, p3152_1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h3017, hlam, p3152_1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h3022, hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h0, h3015, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3131_1, p3152_1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h0, h3015, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3131_1, p3152_1]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h3019, hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h3024, hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h3129, hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [h3130, hlam, p3152_0]
                                            · have p3152_0 := h3152c.1
                                              have p3152_1 := h3152c.2.1
                                              have p3152_2 := h3152c.2.2.1
                                              have p3152_3 := h3152c.2.2.2
                                              linarith only [hlam, p3152_0]
                                          · rcases h4bigk with h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h2109, hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h0, h3015, h3082, h3129, h3130, hc12, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p3131_1, p3186_1, u4elo0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h2109, h3082, h3130, hc23, hlam, hphi, ht34, p3186_1, u4elo1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              rcases p3186_3 (m.d 0 4) (by simp) with h3191 | h3191
                                              · rcases p3186_3 (m.d 1 4) (by simp) with h3192 | h3192
                                                · rcases p3186_3 (m.d 2 4) (by simp) with h3193 | h3193
                                                  · linarith only [h3016, h3193, hlam]
                                                  · linarith only [h3129, h3193, hlam]
                                                · linarith only [h3024, h3192, hlam]
                                              · linarith only [h3191, hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [hc04, hlam, hphi, p3186_1, u4elo1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h0, h3015, h3082, h3129, h3130, hc12, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p3131_1, p3186_1, u4elo1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h3082, h3130, hc23, hlam, hphi, ht34, p3186_1, u4elo1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              rcases p3186_3 (m.d 0 4) (by simp) with h3202 | h3202
                                              · linarith only [h2109, h3202, hlam]
                                              · linarith only [h3019, h3202, hlam]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h3016, hlam, p3186_1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h3021, hlam, p3186_1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h3025, hlam, p3186_1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h0, h3015, h3025, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3131_1, p3186_1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h3017, hlam, p3186_1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h3022, hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h0, h3015, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3131_1, p3186_1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h0, h3015, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3131_1, p3186_1]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h3019, hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h3024, hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h3129, hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [h3130, hlam, p3186_0]
                                            · have p3186_0 := h3186c.1
                                              have p3186_1 := h3186c.2.1
                                              have p3186_2 := h3186c.2.2.1
                                              have p3186_3 := h3186c.2.2.2
                                              linarith only [hlam, p3186_0]
                                          · linarith only [h0, h3015, h3082, h3130, h3151, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3131_1]
                                          · linarith only [h0, h3015, h3151, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3131_1]
                                          · linarith only [h0, h3015, h3130, h3151, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3131_1]
                                  · linarith only [h3022, h3144, hlam]
                                · linarith only [h3143, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                rcases p3131_3 (m.d 0 3) (by simp) with h3225 | h3225
                                · rcases p3131_3 (m.d 1 3) (by simp) with h3226 | h3226
                                  · rcases p3131_3 (m.d 2 3) (by simp) with h3227 | h3227
                                    · linarith only [h3015, h3227, hlam]
                                    · rcases p3131_3 (m.d 3 4) (by simp) with h3229 | h3229
                                      · linarith only [h3017, h3229, hlam]
                                      · linarith only [h3130, h3229, hlam]
                                  · linarith only [h3023, h3226, hlam]
                                · linarith only [h3225, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3017, h3020, h3082, h3130, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3131_1]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                rcases p3131_3 (m.d 0 3) (by simp) with h3236 | h3236
                                · linarith only [h1845, h3236, hlam]
                                · linarith only [h3015, h3236, hlam]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                rcases p3131_3 (m.d 0 3) (by simp) with h3239 | h3239
                                · linarith only [h1845, h3239, hlam]
                                · linarith only [h3017, h3239, hlam]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                rcases p3131_3 (m.d 0 3) (by simp) with h3242 | h3242
                                · linarith only [h1845, h3242, hlam]
                                · linarith only [h3018, h3242, hlam]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3015, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3020, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3025, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3082, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3017, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3022, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3017, hc23, hlam, hphi, ht34, p3131_1, u4elo0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h2109, h3017, h3082, hc23, hlam, hphi, ht34, p3131_1, u4elo1]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3018, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3023, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h2109, h3018, h3019, hc23, hlam, hphi, ht34, p3131_1, u4elo1]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [h3130, hlam, p3131_0]
                              · have p3131_0 := h3131c.1
                                have p3131_1 := h3131c.2.1
                                have p3131_2 := h3131c.2.2.1
                                have p3131_3 := h3131c.2.2.2
                                linarith only [hlam, p3131_0]
                            · linarith only [h2109, h3019, h3130, hc34, hlam, hphi, u4elo1]
                          · linarith only [h2109, h3019, h3129, hc24, hlam, hphi, u4elo1]
                    · linarith only [h2109, h3019, h3024, hlam]
                  · linarith only [h1845, h2109, h3018, h3019, h3023, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h1845, h3017, h3022, hlam]
              · linarith only [h0, h3021, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h3015, h3020, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3267 | h3267
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3268 | h3268
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3269 | h3269
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3270 | h3270
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3271 | h3271
                    · linarith only [h3019, h3271, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2109, h3271, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h2109, h3015, h3018, h3269, h3270, hc01, hc12, hlam, hphi]
                · linarith only [h1845, h3017, h3269, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
              · linarith only [h0, h3016, h3019, h3268, hc02, hlam, hphi, ht23, ht34, u4elo4]
            · linarith only [h0, h3015, h3267, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3278 | h3278
          · linarith only [h3017, h3018, h3278, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3280 | h3280
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3281 | h3281
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3282 | h3282
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3283 | h3283
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3284 | h3284
                    · linarith only [h3278, h3284, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2109, h3284, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3287 | h3287
                    · linarith only [h2109, h3278, h3287, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2109, h3287, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1845, h3282, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3281, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h3015, h3280, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3293 | h3293
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3294 | h3294
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3295 | h3295
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3296 | h3296
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3297 | h3297
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3298 | h3298
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3299 | h3299
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3300 | h3300
                      · linarith only [h3015, h3017, h3300, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3302 | h3302
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3303 | h3303
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3304 | h3304
                            · rcases h3bigk with h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h1845, hlam, p3305_1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3017, h3295, h3297, h3302, h3304, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3305_1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3017, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3017, h3297, h3304, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3305_1, u4elo1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                rcases p3305_3 (m.d 0 3) (by simp) with h3311 | h3311
                                · linarith only [h1845, h3311, hlam]
                                · rcases p3305_3 (m.d 1 3) (by simp) with h3313 | h3313
                                  · rcases p3305_3 (m.d 2 3) (by simp) with h3314 | h3314
                                    · linarith only [h3295, h3314, hlam]
                                    · rcases p3305_3 (m.d 3 4) (by simp) with h3316 | h3316
                                      · linarith only [h3297, h3316, hlam]
                                      · linarith only [h3017, h3316, hlam]
                                  · linarith only [h1845, h3313, hlam]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                rcases p3305_3 (m.d 0 3) (by simp) with h3321 | h3321
                                · linarith only [h1845, h3321, hlam]
                                · linarith only [h3015, h3321, hlam]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h1845, h3017, h3295, hc01, hc12, hlam, hphi, p3305_1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3015, h3017, h3297, h3302, hlam, p3305_2]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3015, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3295, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3300, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3015, h3017, h3304, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3305_1, u4elo3]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hc03, hlam, hphi, ht34, p3305_1, u4elo3]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3297, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3297, hc23, hlam, hphi, ht34, p3305_1, u4elo1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                rcases p3305_3 (m.d 0 3) (by simp) with h3335 | h3335
                                · linarith only [h3017, h3335, hlam]
                                · linarith only [h3293, h3335, hlam]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3293, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3298, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3302, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3304, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, p3305_0]
                            · linarith only [h3017, h3304, hc03, hlam, hphi, ht34, u4elo4]
                          · linarith only [h3017, h3293, h3294, h3297, h3303, hc24, hlam, hphi, u4elo1]
                        · linarith only [h3017, h3293, h3297, h3302, hc23, hlam, hphi, ht34, u4elo1]
                    · linarith only [h3017, h3293, h3294, h3297, h3299, hlam]
                  · linarith only [h3017, h3293, h3297, h3298, hlam]
                · linarith only [h1845, h3297, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3296, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h3015, h3295, hlam]
          · linarith only [h3017, h3293, h3294, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3352 | h3352
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3353 | h3353
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3354 | h3354
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3355 | h3355
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3356 | h3356
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3357 | h3357
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3358 | h3358
                      · linarith only [h3015, h3017, h3358, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3360 | h3360
                        · linarith only [h3015, h3293, h3360, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3362 | h3362
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3363 | h3363
                            · rcases h3bigk with h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c | h3364c
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h1845, hlam, p3364_1]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3293, h3353, h3355, h3363, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3364_1]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3017, hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3293, hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                rcases p3364_3 (m.d 0 3) (by simp) with h3370 | h3370
                                · linarith only [h1845, h3370, hlam]
                                · rcases p3364_3 (m.d 1 3) (by simp) with h3372 | h3372
                                  · rcases p3364_3 (m.d 2 3) (by simp) with h3373 | h3373
                                    · linarith only [h3353, h3373, hlam]
                                    · rcases p3364_3 (m.d 3 4) (by simp) with h3375 | h3375
                                      · linarith only [h3355, h3375, hlam]
                                      · linarith only [h3017, h3375, hlam]
                                  · linarith only [h1845, h3372, hlam]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                rcases p3364_3 (m.d 0 3) (by simp) with h3380 | h3380
                                · linarith only [h1845, h3380, hlam]
                                · linarith only [h3015, h3380, hlam]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h1845, h3293, h3363, hc01, hc13, hlam, hphi, p3364_1]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h1845, h3293, h3353, hc01, hc12, hlam, hphi, p3364_1]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3015, hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3353, hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3358, hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3360, hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h1845, h3355, hc01, hlam, hphi, ht12, ht23, ht34, p3364_1, u4elo1]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3355, hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3355, hc23, hlam, hphi, ht34, p3364_1, u4elo1]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h1845, h3293, h3355, hc01, hlam, hphi, ht12, ht23, ht34, p3364_1, u4elo1]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h1845, h3353, h3356, hc01, hc12, hlam, hphi, p3364_1]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3356, hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3356, h3357, hc23, hlam, hphi, ht34, p3364_1, u4elo1]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [h3363, hlam, p3364_0]
                              · have p3364_0 := h3364c.1
                                have p3364_1 := h3364c.2.1
                                have p3364_2 := h3364c.2.2.1
                                have p3364_3 := h3364c.2.2.2
                                linarith only [hlam, p3364_0]
                            · linarith only [h3016, h3362, h3363, hc34, hlam, hphi, u4elo0]
                          · linarith only [h3017, h3352, h3355, h3362, hc24, hlam, hphi, u4elo1]
                    · linarith only [h3017, h3352, h3355, h3357, hlam]
                  · linarith only [h1845, h3017, h3355, h3356, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h1845, h3355, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3354, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h3015, h3353, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3407 | h3407
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3408 | h3408
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3409 | h3409
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3410 | h3410
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3411 | h3411
                    · linarith only [h3352, h3411, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2109, h3411, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h1845, h3017, h3409, h3410, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h1845, h3409, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3408, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h3015, h3407, hlam]
    · linarith only [h3015, h3016, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3419 | h3419
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3420 | h3420
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3421 | h3421
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3422 | h3422
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3423 | h3423
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3424 | h3424
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3425 | h3425
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3426 | h3426
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3427 | h3427
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3428 | h3428
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3429 | h3429
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3430 | h3430
                          · linarith only [h3015, h3419, h3423, h3430, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h3422, h3430, hc24, hlam, hphi, u4elo0]
                        · linarith only [h3015, h3419, h3421, h3428, h3429, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h3015, h3419, h3428, hc24, hlam, hphi, u4elo3]
                    · linarith only [h3422, h3427, hc14, hlam, hphi, u4elo0]
                  · linarith only [h1845, h3421, h3426, hlam]
                · linarith only [h1845, h3015, h3419, h3420, h3423, h3425, hc01, hc12, hlam, hphi]
              · linarith only [h3015, h3423, h3424, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3439 | h3439
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3440 | h3440
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3441 | h3441
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3442 | h3442
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3443 | h3443
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3444 | h3444
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3445 | h3445
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3446 | h3446
                            · rcases h3bigk with h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h1845, hlam, p3447_1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3015, hlam, p3447_1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                rcases p3447_3 (m.d 0 3) (by simp) with h3451 | h3451
                                · rcases p3447_3 (m.d 1 3) (by simp) with h3452 | h3452
                                  · rcases p3447_3 (m.d 2 3) (by simp) with h3453 | h3453
                                    · rcases p3447_3 (m.d 3 4) (by simp) with h3454 | h3454
                                      · linarith only [h3454, hlam, p3447_0]
                                      · rcases p3447_3 (m.d 3 5) (by simp) with h3456 | h3456
                                        · linarith only [h3421, h3456, hlam]
                                        · rcases h3emin with h3458 | h3458 | h3458 | h3458 | h3458
                                          · rcases h4bigk with h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c | h3459c
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h2109, hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3443, h3446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3459_1, u4elo0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3459_1, u4elo0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              rcases p3459_3 (m.d 0 4) (by simp) with h3464 | h3464
                                              · rcases p3459_3 (m.d 1 4) (by simp) with h3465 | h3465
                                                · rcases p3459_3 (m.d 2 4) (by simp) with h3466 | h3466
                                                  · linarith only [h3419, h3466, hlam]
                                                  · linarith only [h3445, h3466, hlam]
                                                · linarith only [h3442, h3465, hlam]
                                              · linarith only [h3464, hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [hc04, hlam, hphi, p3459_1, u4elo1]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3443, h3446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3459_1, u4elo1]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3459_1, u4elo1]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              rcases p3459_3 (m.d 0 4) (by simp) with h3475 | h3475
                                              · linarith only [h2109, h3475, hlam]
                                              · linarith only [h3422, h3475, hlam]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3419, hlam, p3459_1]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3439, hlam, p3459_1]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3419, h3446, hc02, hc45, hlam, hphi, ht0b, ht5b, p3459_1]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h0, h3419, h3423, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3459_1]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3420, hlam, p3459_1]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3440, hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3443, hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3015, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3447_1, p3459_1]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3422, hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3442, hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3445, hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [h3446, hlam, p3459_0]
                                            · have p3459_0 := h3459c.1
                                              have p3459_1 := h3459c.2.1
                                              have p3459_2 := h3459c.2.2.1
                                              have p3459_3 := h3459c.2.2.2
                                              linarith only [hlam, p3459_0]
                                          · rcases h4bigk with h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c | h3493c
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h2109, hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h2109, hc24, hlam, hphi, p3493_1, u4elo1]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h2109, hc34, hlam, hphi, p3493_1, u4elo1]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              rcases p3493_3 (m.d 0 4) (by simp) with h3498 | h3498
                                              · rcases p3493_3 (m.d 1 4) (by simp) with h3499 | h3499
                                                · rcases p3493_3 (m.d 2 4) (by simp) with h3500 | h3500
                                                  · linarith only [h3419, h3500, hlam]
                                                  · linarith only [h3445, h3500, hlam]
                                                · linarith only [h3442, h3499, hlam]
                                              · linarith only [h3498, hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [hc04, hlam, hphi, p3493_1, u4elo1]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3443, h3446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3493_1, u4elo1]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3493_1, u4elo1]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              rcases p3493_3 (m.d 0 4) (by simp) with h3509 | h3509
                                              · linarith only [h2109, h3509, hlam]
                                              · linarith only [h3422, h3509, hlam]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3419, hlam, p3493_1]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3439, hlam, p3493_1]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3419, h3446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3493_1, u4elo0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h0, h3419, h3423, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3493_1]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3420, hlam, p3493_1]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3440, hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3443, hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h1845, h3423, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3447_1, p3493_1]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3422, hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3442, hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3445, hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [h3446, hlam, p3493_0]
                                            · have p3493_0 := h3493c.1
                                              have p3493_1 := h3493c.2.1
                                              have p3493_2 := h3493c.2.2.1
                                              have p3493_3 := h3493c.2.2.2
                                              linarith only [hlam, p3493_0]
                                          · rcases h4bigk with h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h2109, hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h2109, hc24, hlam, hphi, p3527_1, u4elo1]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h2109, hc34, hlam, hphi, p3527_1, u4elo1]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              rcases p3527_3 (m.d 0 4) (by simp) with h3532 | h3532
                                              · rcases p3527_3 (m.d 1 4) (by simp) with h3533 | h3533
                                                · rcases p3527_3 (m.d 2 4) (by simp) with h3534 | h3534
                                                  · linarith only [h3419, h3534, hlam]
                                                  · linarith only [h3445, h3534, hlam]
                                                · linarith only [h3442, h3533, hlam]
                                              · linarith only [h3532, hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [hc04, hlam, hphi, p3527_1, u4elo1]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3443, h3446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3527_1, u4elo1]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3527_1, u4elo1]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              rcases p3527_3 (m.d 0 4) (by simp) with h3543 | h3543
                                              · linarith only [h2109, h3543, hlam]
                                              · linarith only [h3422, h3543, hlam]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3419, hlam, p3527_1]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3439, hlam, p3527_1]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3419, h3446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3527_1, u4elo0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h0, h3419, h3423, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3527_1]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3420, hlam, p3527_1]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3440, hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3443, hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h1845, h3423, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3447_1, p3527_1]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3422, hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3442, hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3445, hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [h3446, hlam, p3527_0]
                                            · have p3527_0 := h3527c.1
                                              have p3527_1 := h3527c.2.1
                                              have p3527_2 := h3527c.2.2.1
                                              have p3527_3 := h3527c.2.2.2
                                              linarith only [hlam, p3527_0]
                                          · linarith only [h3458, hlam, ht34, u4elo3]
                                          · linarith only [h0, h3419, h3423, h3444, h3445, h3458, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                    · linarith only [h3443, h3453, hlam]
                                  · linarith only [h3440, h3452, hlam]
                                · linarith only [h3451, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                rcases p3447_3 (m.d 0 3) (by simp) with h3566 | h3566
                                · rcases p3447_3 (m.d 1 3) (by simp) with h3567 | h3567
                                  · rcases p3447_3 (m.d 2 3) (by simp) with h3568 | h3568
                                    · rcases p3447_3 (m.d 3 4) (by simp) with h3569 | h3569
                                      · linarith only [h3420, h3569, hlam]
                                      · linarith only [h3446, h3569, hlam]
                                    · linarith only [h3444, h3568, hlam]
                                  · linarith only [h3441, h3567, hlam]
                                · linarith only [h3566, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3015, h3419, h3423, h3445, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3447_1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3423, hlam, p3447_1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                rcases p3447_3 (m.d 0 3) (by simp) with h3578 | h3578
                                · linarith only [h1845, h3578, hlam]
                                · linarith only [h3420, h3578, hlam]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                rcases p3447_3 (m.d 0 3) (by simp) with h3581 | h3581
                                · linarith only [h1845, h3581, hlam]
                                · linarith only [h3421, h3581, hlam]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3015, h3419, h3443, h3446, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3447_1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h1845, hc01, hc23, hlam, hphi, ht12, p3447_1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                rcases p3447_3 (m.d 0 3) (by simp) with h3587 | h3587
                                · linarith only [h3015, h3587, hlam]
                                · linarith only [h3420, h3587, hlam]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                rcases p3447_3 (m.d 0 3) (by simp) with h3590 | h3590
                                · linarith only [h3015, h3590, hlam]
                                · linarith only [h3421, h3590, hlam]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3420, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3440, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3443, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3015, h3419, h3443, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p3447_1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3421, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3441, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3444, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3446, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hlam, p3447_0]
                            · linarith only [h2109, h3422, h3446, hc34, hlam, hphi, u4elo1]
                          · linarith only [h2109, h3422, h3445, hc24, hlam, hphi, u4elo1]
                        · linarith only [h0, h3423, h3444, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h2109, h3423, h3439, h3443, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h2109, h3419, h3422, h3442, hc01, hc12, hlam, hphi]
                  · linarith only [h1845, h2109, h3421, h3422, h3441, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h3423, h3440, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3439, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3611 | h3611
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3612 | h3612
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3613 | h3613
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3614 | h3614
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3615 | h3615
                    · linarith only [h3422, h3615, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2109, h3615, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h3015, h3419, h3421, h3611, h3614, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1845, h3613, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h3015, h3611, h3612, hc03, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3621 | h3621
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3622 | h3622
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3623 | h3623
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3624 | h3624
                    · linarith only [h2109, h3422, h3624, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2109, h3624, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h1845, h3421, h3623, hlam]
                · linarith only [h1845, h3420, h3622, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
              · linarith only [h0, h3621, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3630 | h3630
          · linarith only [h3015, h3419, h3421, h3630, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3632 | h3632
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3633 | h3633
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3634 | h3634
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3635 | h3635
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3636 | h3636
                    · linarith only [h3630, h3636, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2109, h3636, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3639 | h3639
                    · linarith only [h2109, h3015, h3419, h3630, h3632, h3635, h3639, hc01, hc24, hc35, hlam, hphi, ht12, ht23, u4elo1]
                    · linarith only [h2109, h3015, h3419, h3632, h3635, h3639, hc01, hc24, hc35, hlam, hphi, ht12, ht23, u4elo4]
                · linarith only [h3015, h3419, h3420, h3632, h3634, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h3632, h3633, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3644 | h3644
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3645 | h3645
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3646 | h3646
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3647 | h3647
                    · linarith only [h3015, h3419, h3421, h3630, h3647, hc24, hlam, hphi, u4elo1]
                    · linarith only [h2109, h3015, h3419, h3421, h3632, h3646, h3647, hc01, hc23, hc24, hlam, hphi, ht12, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3650 | h3650
                    · linarith only [h2109, h3630, h3632, h3644, h3646, h3650, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h2109, h3650, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h3420, h3632, h3645, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
              · linarith only [h0, h3419, h3644, hlam]
      · linarith only [h3015, h3419, h3420, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3656 | h3656
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3657 | h3657
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3658 | h3658
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3659 | h3659
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3660 | h3660
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3661 | h3661
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3662 | h3662
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3663 | h3663
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3664 | h3664
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3665 | h3665
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3666 | h3666
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3667 | h3667
                            · rcases h3bigk with h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h1845, hlam, p3668_1]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3015, hlam, p3668_1]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3015, h3659, h3667, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3668_1]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                rcases p3668_3 (m.d 0 3) (by simp) with h3673 | h3673
                                · rcases p3668_3 (m.d 1 3) (by simp) with h3674 | h3674
                                  · rcases p3668_3 (m.d 2 3) (by simp) with h3675 | h3675
                                    · rcases p3668_3 (m.d 3 4) (by simp) with h3676 | h3676
                                      · linarith only [h3656, h3676, hlam]
                                      · linarith only [h3667, h3676, hlam]
                                    · linarith only [h3665, h3675, hlam]
                                  · linarith only [h3662, h3674, hlam]
                                · linarith only [h3673, hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3656, h3667, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p3668_1]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h0, h3015, h3659, hc01, hc12, hlam, hphi, p3668_1]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                rcases p3668_3 (m.d 0 3) (by simp) with h3685 | h3685
                                · linarith only [h1845, h3685, hlam]
                                · linarith only [h3656, h3685, hlam]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                rcases p3668_3 (m.d 0 3) (by simp) with h3688 | h3688
                                · linarith only [h1845, h3688, hlam]
                                · linarith only [h3657, h3688, hlam]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3656, h3667, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3668_1]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3659, hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3659, h3667, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3668_1]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                rcases p3668_3 (m.d 0 3) (by simp) with h3695 | h3695
                                · linarith only [h3015, h3695, hlam]
                                · linarith only [h3657, h3695, hlam]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3656, hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3661, hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3664, hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3015, h3656, h3659, h3667, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3668_1]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3657, hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3662, hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3665, hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [h3667, hlam, p3668_0]
                              · have p3668_0 := h3668c.1
                                have p3668_1 := h3668c.2.1
                                have p3668_2 := h3668c.2.2.1
                                have p3668_3 := h3668c.2.2.2
                                linarith only [hlam, p3668_0]
                            · linarith only [h3419, h3658, h3660, h3667, hc34, hlam, hphi, u4elo1]
                          · linarith only [h3419, h3658, h3666, hlam]
                        · linarith only [h3015, h3657, h3665, hlam]
                      · linarith only [h0, h3015, h3664, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h3419, h3658, h3660, h3663, hlam]
                  · linarith only [h1845, h3015, h3657, h3662, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h1845, h3661, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3660, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3716 | h3716
              · linarith only [h0, h3419, h3659, h3716, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3716, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3719 | h3719
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3720 | h3720
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3721 | h3721
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3722 | h3722
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3723 | h3723
                    · linarith only [h3658, h3723, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2109, h3723, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h1845, h3657, h3722, hlam]
                · linarith only [h1845, h3721, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h3015, h3719, h3720, hc03, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3729 | h3729
              · linarith only [h0, h3419, h3719, h3729, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3729, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3732 | h3732
          · linarith only [h3656, h3657, h3732, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3734 | h3734
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3735 | h3735
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3736 | h3736
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3737 | h3737
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3738 | h3738
                    · linarith only [h3732, h3738, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2109, h3738, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3741 | h3741
                    · linarith only [h0, h3419, h3732, h3741, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2109, h3741, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1845, h3736, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3735, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3746 | h3746
              · linarith only [h0, h3419, h3734, h3746, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3746, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3749 | h3749
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3750 | h3750
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3751 | h3751
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3752 | h3752
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3753 | h3753
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3754 | h3754
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3755 | h3755
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3756 | h3756
                      · linarith only [h0, h3015, h3656, h3751, h3756, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h3015, h3753, h3756, hc01, hc13, hlam, hphi]
                    · linarith only [h2109, h3755, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h1845, h3749, h3754, hlam]
                · linarith only [h3015, h3751, h3753, hc02, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h0, h3752, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3763 | h3763
              · linarith only [h0, h3419, h3751, h3763, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3763, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h3656, h3749, h3750, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3767 | h3767
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3768 | h3768
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3769 | h3769
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3770 | h3770
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3771 | h3771
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3772 | h3772
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3773 | h3773
                      · linarith only [h0, h3015, h3656, h3768, h3773, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h3015, h3770, h3773, hc01, hc13, hlam, hphi]
                    · linarith only [h2109, h3772, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h3015, h3656, h3770, h3771, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h1845, h3770, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3769, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3780 | h3780
              · linarith only [h0, h3419, h3768, h3780, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3780, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3783 | h3783
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3784 | h3784
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3785 | h3785
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3786 | h3786
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3787 | h3787
                    · linarith only [h3767, h3787, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2109, h3787, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h3015, h3656, h3785, h3786, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h1845, h3785, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3784, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3793 | h3793
              · linarith only [h0, h3419, h3783, h3793, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3793, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1845 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2109 | h2109
  · exact r1l7_13_24_L_I_M_LI_x1_x1_x0 m hb3 hb4 h0 h1845 h2109
  · exact r1l7_13_24_L_I_M_LI_x1_x1_x1 m hb3 hb4 h0 h1845 h2109

set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1845 | h1845
  · exact r1l7_13_24_L_I_M_LI_x1_x0 m hb3 hb4 h0 h1845
  · exact r1l7_13_24_L_I_M_LI_x1_x1 m hb3 hb4 h0 h1845

set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_13_24_L_I_M_LI_x0 m hb3 hb4 h0
  · exact r1l7_13_24_L_I_M_LI_x1 m hb3 hb4 h0

end R2N4
