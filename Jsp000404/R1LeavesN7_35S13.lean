import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_35S10
import Jsp000404.R1LeavesN7_35S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2134 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3273 | h3273
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3274 | h3274
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3275 | h3275
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3276 | h3276
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3277 | h3277
          · linarith only [h2134, h3273, h3276, h3277, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3279 | h3279
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3280 | h3280
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3281 | h3281
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3282 | h3282
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3283 | h3283
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3284 | h3284
                      · linarith only [h0, h3273, h3277, h3284, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases h2bigk with h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c | h3286c
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h0, hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h2134, hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h0, h3277, h3282, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3286_1]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h0, h3277, h3283, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3286_1, u5ehi3]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3277, hc02, hc23, hlam, hphi, p3286_1]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3277, hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3277, h3282, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3286_1]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3277, h3283, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3286_1, u5ehi3]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3273, h3276, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3286_1, u5ehi4]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3286_1]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          rcases p3286_3 (m.d 0 2) (by simp) with h3300 | h3300
                          · linarith only [h2134, h3300, hlam]
                          · linarith only [h3273, h3300, hlam]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3283, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3286_1, u5ehi3]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3273, hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3279, hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3282, hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3284, hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3274, hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3280, hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3283, hlam, p3286_0]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [h3274, h3282, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3286_1]
                        · have p3286_0 := h3286c.1
                          have p3286_1 := h3286c.2.1
                          have p3286_2 := h3286c.2.2.1
                          have p3286_3 := h3286c.2.2.2
                          linarith only [hlam, p3286_0]
                    · linarith only [h0, h3274, h3277, h3283, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h3273, h3276, h3277, h3282, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · linarith only [h0, h3273, h3275, h3277, h3281, hlam]
              · linarith only [h0, h3274, h3280, hlam]
            · linarith only [h0, h3273, h3279, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3319 | h3319
          · linarith only [h2134, h3274, h3319, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3321 | h3321
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3322 | h3322
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3323 | h3323
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3324 | h3324
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3325 | h3325
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3326 | h3326
                      · linarith only [h0, h3273, h3276, h3319, h3326, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases h2bigk with h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h0, hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h2134, hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h0, h3319, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3328_1]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h0, h3319, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3328_1, u5ehi2]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3319, hc02, hc23, hlam, hphi, p3328_1]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3319, hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3319, h3324, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3328_1]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3319, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3328_1, u5ehi2]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3274, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3328_1, u5ehi2]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p3328_1]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          rcases p3328_3 (m.d 0 2) (by simp) with h3342 | h3342
                          · linarith only [h2134, h3342, hlam]
                          · linarith only [h3273, h3342, hlam]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3325, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3328_1, u5ehi3]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3273, hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3321, hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3324, hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3326, hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3274, hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3322, hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3325, hlam, p3328_0]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [h3274, h3324, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3328_1]
                        · have p3328_0 := h3328c.1
                          have p3328_1 := h3328c.2.1
                          have p3328_2 := h3328c.2.2.1
                          have p3328_3 := h3328c.2.2.2
                          linarith only [hlam, p3328_0]
                    · linarith only [h0, h3274, h3319, h3325, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h3274, h3319, h3324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h0, h3274, h3275, h3276, h3319, h3323, hlam]
              · linarith only [h0, h3274, h3322, hlam]
            · linarith only [h0, h3273, h3321, hlam]
      · linarith only [h2134, h3273, h3275, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3362 | h3362
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3363 | h3363
        · linarith only [h3273, h3274, h3363, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3365 | h3365
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3366 | h3366
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3367 | h3367
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3368 | h3368
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3369 | h3369
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3370 | h3370
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3371 | h3371
                      · linarith only [h3273, h3274, h3363, h3365, h3370, h3371, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h2bigk with h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h0, hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h2134, hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3274, h3365, h3370, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3373_1]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3274, hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p3373_1]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3370, hc12, hlam, hphi, ht01, ht0b, ht5b, p3373_1, u5ehi2]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          rcases p3373_3 (m.d 0 2) (by simp) with h3382 | h3382
                          · linarith only [h0, h3382, hlam]
                          · linarith only [h3273, h3382, hlam]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3273, h3274, h3369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3373_1]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3273, h3365, h3369, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3373_1]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3365, hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3365, h3369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3373_1]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3273, h3274, h3365, h3369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3373_1]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3273, hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3366, hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3369, hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3371, hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3273, h3367, h3369, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3373_1]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3367, hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3370, hlam, p3373_0]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [h3365, h3369, h3370, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3373_1]
                        · have p3373_0 := h3373c.1
                          have p3373_1 := h3373c.2.1
                          have p3373_2 := h3373c.2.2.1
                          have p3373_3 := h3373c.2.2.2
                          linarith only [hlam, p3373_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3401 | h3401
                      · linarith only [h2134, h3273, h3370, h3401, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases h2bigk with h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h0, hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h2134, hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h2134, h3370, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3403_1]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3274, hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p3403_1]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h2134, h3273, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3403_1]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          rcases p3403_3 (m.d 0 2) (by simp) with h3412 | h3412
                          · linarith only [h0, h3412, hlam]
                          · linarith only [h3273, h3412, hlam]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p3403_1, u5ehi2]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3273, h3369, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3403_1]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3365, hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3365, h3369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3403_1]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3370, hlam, p3403_1]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3273, hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3366, hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3369, hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3401, hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3273, h3369, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3403_1]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3367, hlam, p3403_0]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h2134, h3367, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3403_1]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [h3367, h3369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3403_1]
                        · have p3403_0 := h3403c.1
                          have p3403_1 := h3403c.2.1
                          have p3403_2 := h3403c.2.2.1
                          have p3403_3 := h3403c.2.2.2
                          linarith only [hlam, p3403_0]
                  · linarith only [h2134, h3362, h3369, hlam]
                · linarith only [h2134, h3273, h3362, h3365, h3368, hlam]
              · linarith only [h2134, h3365, h3367, hc02, hc25, hlam, hphi]
            · linarith only [h2134, h3273, h3365, h3366, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3435 | h3435
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3436 | h3436
              · linarith only [h3273, h3274, h3365, h3436, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3438 | h3438
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3439 | h3439
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3440 | h3440
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3441 | h3441
                      · linarith only [h0, h3273, h3436, h3440, h3441, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases h2bigk with h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h0, hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h2134, hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h0, h3436, h3441, hc24, hc45, hlam, hphi, p3443_1]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3274, hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3436, h3441, hc02, hc45, hlam, hphi, ht23, ht34, p3443_1]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3365, hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3436, h3441, hc24, hc45, hlam, hphi, p3443_1]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3436, hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3273, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3443_1]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p3443_1]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          rcases p3443_3 (m.d 0 2) (by simp) with h3457 | h3457
                          · linarith only [h2134, h3457, hlam]
                          · linarith only [h3273, h3457, hlam]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3436, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3443_1, u5ehi1]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3273, hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3435, hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3439, hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3441, hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3273, h3439, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3443_1]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3443_1]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3440, hlam, p3443_0]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [h3439, h3441, hc34, hc45, hlam, hphi, p3443_1]
                        · have p3443_0 := h3443c.1
                          have p3443_1 := h3443c.2.1
                          have p3443_2 := h3443c.2.2.1
                          have p3443_3 := h3443c.2.2.2
                          linarith only [hlam, p3443_0]
                    · linarith only [h0, h3365, h3440, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h3365, h3439, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h3273, h3362, h3365, h3438, hlam]
            · linarith only [h0, h3273, h3435, hlam]
      · linarith only [h2134, h3273, h3362, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3476 | h3476
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3477 | h3477
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3478 | h3478
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3479 | h3479
          · linarith only [h2134, h3476, h3479, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3481 | h3481
            · linarith only [h3273, h3476, h3479, h3481, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3483 | h3483
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3484 | h3484
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3485 | h3485
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3486 | h3486
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3487 | h3487
                      · rcases h2bigk with h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h0, hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h2134, hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3273, hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3486, hc02, hlam, hphi, ht0b, ht5b, p3488_1, u5ehi3]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3481, h3485, hc02, hc23, hlam, hphi, p3488_1]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3479, hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3481, hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3481, h3485, h3486, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3488_1, u5ehi3]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3476, h3486, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3488_1, u5ehi3]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3488_1]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3273, h3476, h3486, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3488_1, u5ehi3]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3486, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3488_1, u5ehi3]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3476, h3486, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3488_1, u5ehi3]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h0, h3476, h3486, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3488_1, u5ehi3]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3485, hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3485, h3486, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3488_1, u5ehi3]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3476, hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3483, hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3486, hlam, p3488_0]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [h3487, hlam, p3488_1]
                        · have p3488_0 := h3488c.1
                          have p3488_1 := h3488c.2.1
                          have p3488_2 := h3488c.2.2.1
                          have p3488_3 := h3488c.2.2.2
                          linarith only [hlam, p3488_0]
                      · linarith only [h3273, h3476, h3486, h3487, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · linarith only [h2134, h3476, h3486, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h2134, h3477, h3485, hlam]
                · linarith only [h0, h3476, h3477, h3479, h3484, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h3476, h3483, hlam]
        · linarith only [h3273, h3476, h3478, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3520 | h3520
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3521 | h3521
          · linarith only [h2134, h3476, h3521, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3523 | h3523
            · linarith only [h3273, h3476, h3523, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3525 | h3525
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3526 | h3526
                · linarith only [h2134, h3476, h3477, h3526, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3528 | h3528
                  · linarith only [h0, h3521, h3526, h3528, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h2134, h3476, h3528, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
              · linarith only [h0, h3476, h3525, hlam]
        · linarith only [h2134, h3476, h3477, h3520, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3533 | h3533
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3534 | h3534
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3535 | h3535
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3536 | h3536
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3537 | h3537
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3538 | h3538
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3539 | h3539
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3540 | h3540
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3541 | h3541
                      · rcases h2bigk with h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c | h3542c
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h0, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h2134, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3273, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3476, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p3542_1]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3539, h3541, hc12, hlam, hphi, ht01, ht0b, ht5b, p3542_1, u5ehi2]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h0, h3273, hc01, hc12, hlam, hphi, p3542_1]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h0, h3476, hc01, hc12, hlam, hphi, p3542_1]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3542_1]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3535, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3273, h3534, h3535, hc12, hlam, hphi, ht01, ht0b, ht5b, p3542_1, u5ehi4]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h0, h3476, h3535, hc01, hc12, hlam, hphi, p3542_1]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h0, h3536, hc01, hc14, hlam, hphi, p3542_1]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3536, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3539, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h0, h3476, h3536, h3538, hc01, hc13, hlam, hphi, p3542_1]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h0, h3537, hc01, hc15, hlam, hphi, p3542_1]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3537, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3540, hlam, p3542_0]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [h3541, hlam, p3542_1]
                        · have p3542_0 := h3542c.1
                          have p3542_1 := h3542c.2.1
                          have p3542_2 := h3542c.2.2.1
                          have p3542_3 := h3542c.2.2.2
                          linarith only [hlam, p3542_0]
                      · linarith only [h0, h2134, h3273, h3533, h3534, h3535, h3541, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3569 | h3569
                      · linarith only [h3539, h3540, h3569, hlam]
                      · linarith only [h0, h2134, h3273, h3533, h3534, h3540, h3569, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h2134, h3533, h3539, hlam]
                · linarith only [h2134, h3533, h3535, h3538, hlam]
              · linarith only [h2134, h3533, h3534, h3535, h3537, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h2134, h3533, h3534, h3535, h3536, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3576 | h3576
            · linarith only [h0, h3273, h3535, h3576, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3578 | h3578
              · linarith only [h0, h3476, h3535, h3578, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3580 | h3580
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3581 | h3581
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3582 | h3582
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3583 | h3583
                      · rcases h2bigk with h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h0, hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h2134, hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h3273, hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h3476, hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h0, h3578, h3581, h3583, hc01, hc23, hlam, hphi, ht12, p3584_1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h3535, hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h3576, hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h3578, hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3584_1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p3584_1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h3578, h3583, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3584_1, u5ehi1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h0, h3578, hc01, hc23, hlam, hphi, ht12, p3584_1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3584_1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3584_1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h3581, hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h0, h3578, h3581, hc01, hc23, hlam, hphi, ht12, p3584_1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3584_1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3584_1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h3582, hlam, p3584_0]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [h3583, hlam, p3584_1]
                        · have p3584_0 := h3584c.1
                          have p3584_1 := h3584c.2.1
                          have p3584_2 := h3584c.2.2.1
                          have p3584_3 := h3584c.2.2.2
                          linarith only [hlam, p3584_0]
                      · linarith only [h0, h2134, h3273, h3533, h3534, h3583, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h3535, h3582, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h2134, h3533, h3581, hlam]
                · linarith only [h0, h2134, h3533, h3535, h3580, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3614 | h3614
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3615 | h3615
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3616 | h3616
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3617 | h3617
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3618 | h3618
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3619 | h3619
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3620 | h3620
                      · linarith only [h0, h3273, h3534, h3615, h3620, hc01, hc12, hlam, hphi]
                      · rcases h2bigk with h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h0, hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h2134, hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h3273, hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h3476, hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p3622_1]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h3476, h3619, hc12, hlam, hphi, ht01, ht0b, ht5b, p3622_1, u5ehi0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h0, h3273, hc01, hc12, hlam, hphi, p3622_1]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h0, h3476, hc01, hc12, hlam, hphi, p3622_1]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3622_1]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h3614, hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h0, h3273, h3614, hc01, hc12, hlam, hphi, p3622_1]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h0, h3476, h3614, hc01, hc12, hlam, hphi, p3622_1]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3622_1]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h3615, hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h3618, hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h3620, hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h0, h3616, hc01, hc15, hlam, hphi, p3622_1]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h3616, hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h3619, hlam, p3622_0]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [h3614, h3619, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3622_1]
                        · have p3622_0 := h3622c.1
                          have p3622_1 := h3622c.2.1
                          have p3622_2 := h3622c.2.2.1
                          have p3622_3 := h3622c.2.2.2
                          linarith only [hlam, p3622_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3648 | h3648
                      · linarith only [h0, h3273, h3534, h3615, h3648, hc01, hc12, hlam, hphi]
                      · rcases h2bigk with h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h0, hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h2134, hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h3273, hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h3476, hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p3650_1]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h0, h2134, hc01, hc12, hlam, hphi, p3650_1]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h0, h3273, hc01, hc12, hlam, hphi, p3650_1]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p3650_1, u5ehi2]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3650_1]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h3614, hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h0, h3273, h3614, hc01, hc12, hlam, hphi, p3650_1]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h3619, hlam, p3650_1]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3650_1]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h3615, hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h3618, hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h3648, hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3650_1]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h3616, hlam, p3650_0]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h2134, h3616, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3650_1]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [h3616, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3650_1]
                        · have p3650_0 := h3650c.1
                          have p3650_1 := h3650c.2.1
                          have p3650_2 := h3650c.2.2.1
                          have p3650_3 := h3650c.2.2.2
                          linarith only [hlam, p3650_0]
                  · linarith only [h2134, h3533, h3618, hlam]
                · linarith only [h2134, h3533, h3614, h3617, hlam]
              · linarith only [h0, h2134, h3614, h3616, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2134, h3614, h3615, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3680 | h3680
            · linarith only [h0, h3273, h3614, h3680, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3682 | h3682
              · linarith only [h0, h3476, h3614, h3682, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3684 | h3684
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3685 | h3685
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3686 | h3686
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3687 | h3687
                      · rcases h2bigk with h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h0, hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h2134, hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h3273, hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h3476, hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h0, h3682, h3685, h3687, hc01, hc23, hlam, hphi, ht12, p3688_1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h3614, hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h3680, hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h3682, hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3688_1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p3688_1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h3682, h3687, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3688_1, u5ehi1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h0, h3682, hc01, hc23, hlam, hphi, ht12, p3688_1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3688_1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3688_1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h3685, hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h0, h3682, h3685, hc01, hc23, hlam, hphi, ht12, p3688_1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3688_1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3688_1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h3686, hlam, p3688_0]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [h3687, hlam, p3688_1]
                        · have p3688_0 := h3688c.1
                          have p3688_1 := h3688c.2.1
                          have p3688_2 := h3688c.2.2.1
                          have p3688_3 := h3688c.2.2.2
                          linarith only [hlam, p3688_0]
                      · linarith only [h0, h3680, h3687, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h3614, h3686, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h3533, h3614, h3685, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h2134, h3533, h3614, h3684, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3718 | h3718
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3719 | h3719
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3720 | h3720
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3721 | h3721
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3722 | h3722
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3723 | h3723
                  · linarith only [h3533, h3718, h3719, h3723, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · linarith only [h0, h2134, h3719, h3722, h3723, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3726 | h3726
                  · linarith only [h3719, h3722, h3726, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3728 | h3728
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3729 | h3729
                      · rcases h2bigk with h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c | h3730c
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h0, hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h2134, hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3273, hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3476, hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p3730_1]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3728, hc12, hlam, hphi, ht01, ht0b, ht5b, p3730_1, u5ehi3]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h0, h3273, hc01, hc12, hlam, hphi, p3730_1]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3476, hc12, hlam, hphi, ht01, ht0b, ht5b, p3730_1, u5ehi0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h0, h3719, hc01, hc13, hlam, hphi, p3730_1]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3719, hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3726, hlam, p3730_1]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h0, h3476, h3719, h3722, hc01, hc34, hlam, hphi, ht12, ht23, p3730_1]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3730_1]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3720, hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3720, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3730_1]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h0, h3476, h3720, hc01, hc12, hlam, hphi, p3730_1]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h0, h3721, hc01, hc15, hlam, hphi, p3730_1]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3721, hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3728, hlam, p3730_0]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [h3729, hlam, p3730_1]
                        · have p3730_0 := h3730c.1
                          have p3730_1 := h3730c.2.1
                          have p3730_2 := h3730c.2.2.1
                          have p3730_3 := h3730c.2.2.2
                          linarith only [hlam, p3730_0]
                      · linarith only [h3273, h3718, h3729, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3757 | h3757
                      · rcases h2bigk with h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h0, hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h2134, hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h3273, hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h3476, hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h0, h2134, hc01, hc12, hlam, hphi, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h3273, h3718, hc12, hlam, hphi, ht01, ht0b, ht5b, p3758_1, u5ehi4]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h0, h3476, hc01, hc12, hlam, hphi, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h3719, hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h3726, hlam, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h3728, hlam, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h3720, hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h3720, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h0, h2134, h3720, h3728, hc01, hc12, hlam, hphi, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h3721, hlam, p3758_0]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h0, h2134, h3721, hc01, hc12, hlam, hphi, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [h3757, hlam, p3758_1]
                        · have p3758_0 := h3758c.1
                          have p3758_1 := h3758c.2.1
                          have p3758_2 := h3758c.2.2.1
                          have p3758_3 := h3758c.2.2.2
                          linarith only [hlam, p3758_0]
                      · linarith only [h3273, h3718, h3757, hlam]
              · linarith only [h3273, h3718, h3720, h3721, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h0, h2134, h3719, h3720, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3787 | h3787
            · linarith only [h0, h3273, h3719, h3787, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3789 | h3789
              · linarith only [h0, h3476, h3719, h3789, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3791 | h3791
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3792 | h3792
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3793 | h3793
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3794 | h3794
                      · rcases h2bigk with h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h2134, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3273, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3476, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, h3789, h3792, h3794, hc01, hc23, hlam, hphi, ht12, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3719, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3787, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3789, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3789, h3794, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3795_1, u5ehi1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, h3789, hc01, hc23, hlam, hphi, ht12, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3792, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, h3789, h3792, hc01, hc23, hlam, hphi, ht12, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3793, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3794, hlam, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hlam, p3795_0]
                      · linarith only [h0, h3273, h3533, h3718, h3794, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h3533, h3718, h3719, h3791, h3793, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h3719, h3791, h3792, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3824 | h3824
                  · linarith only [h0, h3719, h3791, h3824, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3719, h3824, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3827 | h3827
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3828 | h3828
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3829 | h3829
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3830 | h3830
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3831 | h3831
                  · linarith only [h0, h2134, h3533, h3827, h3831, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h2134, h3830, h3831, hc01, hc13, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3834 | h3834
                  · linarith only [h3827, h3830, h3834, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3836 | h3836
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3837 | h3837
                      · linarith only [h0, h2134, h3533, h3718, h3828, h3837, hc01, hc12, hlam, hphi]
                      · linarith only [h3834, h3836, h3837, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3840 | h3840
                      · linarith only [h0, h2134, h3533, h3718, h3828, h3840, hc01, hc12, hlam, hphi]
                      · rcases h2bigk with h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h0, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h2134, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3273, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3476, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h0, h2134, hc01, hc12, hlam, hphi, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h0, h3273, hc01, hc12, hlam, hphi, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h0, h3476, hc01, hc12, hlam, hphi, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3827, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3834, hlam, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3836, hlam, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3828, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3828, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3840, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3829, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h0, h2134, h3829, hc01, hc12, hlam, hphi, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3829, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hlam, p3842_0]
              · linarith only [h0, h2134, h3827, h3829, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2134, h3827, h3828, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3870 | h3870
            · linarith only [h0, h3273, h3827, h3870, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3872 | h3872
              · linarith only [h0, h3476, h3827, h3872, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3874 | h3874
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3875 | h3875
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3876 | h3876
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3877 | h3877
                      · rcases h2bigk with h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h0, hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h2134, hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h3273, hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h3476, hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h0, h3872, h3875, h3877, hc01, hc23, hlam, hphi, ht12, p3878_1]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h3827, hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h3870, hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h3872, hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3878_1]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p3878_1]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h3877, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3878_1, u5ehi2]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h0, h3872, hc01, hc23, hlam, hphi, ht12, p3878_1]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3878_1]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3878_1]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h3875, hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h0, h3872, h3875, hc01, hc23, hlam, hphi, ht12, p3878_1]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3878_1]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3878_1]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h3876, hlam, p3878_0]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [h3877, hlam, p3878_1]
                        · have p3878_0 := h3878c.1
                          have p3878_1 := h3878c.2.1
                          have p3878_2 := h3878c.2.2.1
                          have p3878_3 := h3878c.2.2.2
                          linarith only [hlam, p3878_0]
                      · linarith only [h0, h3870, h3877, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h3827, h3876, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h3827, h3874, h3875, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3907 | h3907
                  · linarith only [h0, h3827, h3874, h3907, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3827, h3907, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2134 | h2134
  · exact r1l7_22_15_H_I_L_R_x1_x0 m hb2 hb5 h0 h2134
  · exact r1l7_22_15_H_I_L_R_x1_x1 m hb2 hb5 h0 h2134

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_15_H_I_L_R_x0 m hb2 hb5 h0
  · exact r1l7_22_15_H_I_L_R_x1 m hb2 hb5 h0

end R2N4
