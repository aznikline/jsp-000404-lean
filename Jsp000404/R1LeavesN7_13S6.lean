import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7926000 in
set_option maxHeartbeats 7926000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2669 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h2986 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h3195 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h3196 | h3196
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3197 | h3197
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3198 | h3198
      · linarith only [h0, h3198, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3200 | h3200
        · linarith only [h0, h2669, h3200, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3202 | h3202
          · linarith only [h0, h2986, h3202, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3204 | h3204
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3205 | h3205
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3206 | h3206
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3207 | h3207
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3208 | h3208
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3209 | h3209
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3210 | h3210
                        · rcases h2bigk with h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h2986, hc12, hc25, hlam, hphi, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h4, hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h2669, hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h2986, hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h0, hlam, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h3198, hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h3200, hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h3202, hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h2, h2669, h3204, h3210, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h0, h2986, hc12, hc23, hlam, hphi, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h3207, hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h0, h2986, h3207, hc12, hc23, hlam, hphi, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h3208, hlam, p3211_0]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [h3209, hlam, p3211_1]
                          · have p3211_0 := h3211c.1
                            have p3211_1 := h3211c.2.1
                            have p3211_2 := h3211c.2.2.1
                            have p3211_3 := h3211c.2.2.2
                            linarith only [hlam, p3211_0]
                        · rcases h2bigk with h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h4, hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h2669, hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h2986, hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h0, hlam, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h3198, hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h3200, hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h3202, hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h0, h2986, hc12, hc23, hlam, hphi, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h3207, hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h0, h2986, h3207, hc12, hc23, hlam, hphi, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h3208, hlam, p3237_0]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [h3209, hlam, p3237_1]
                          · have p3237_0 := h3237c.1
                            have p3237_1 := h3237c.2.1
                            have p3237_2 := h3237c.2.2.1
                            have p3237_3 := h3237c.2.2.2
                            linarith only [hlam, p3237_0]
                      · linarith only [h2669, h3197, h3209, hlam]
                    · linarith only [h3196, h3208, h4, hlam]
                  · linarith only [h3195, h3207, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3266 | h3266
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3267 | h3267
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3268 | h3268
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3269 | h3269
                        · linarith only [h1, h3200, h3204, h3206, h3269, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h2bigk with h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c | h3271c
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h4, hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h2669, hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h2986, hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h0, hlam, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h3198, hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h3200, hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h3202, hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h0, h2986, hc12, hc23, hlam, hphi, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h3266, hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h0, h2986, h3266, hc12, hc23, hlam, hphi, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h3267, hlam, p3271_0]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [h3268, hlam, p3271_1]
                          · have p3271_0 := h3271c.1
                            have p3271_1 := h3271c.2.1
                            have p3271_2 := h3271c.2.2.1
                            have p3271_3 := h3271c.2.2.2
                            linarith only [hlam, p3271_0]
                      · linarith only [h0, h2669, h3195, h3197, h3268, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h3195, h3197, h3205, h3206, h3267, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h3195, h3197, h3204, h3206, h3266, h4, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3300 | h3300
                · linarith only [h3204, h3205, h3300, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3302 | h3302
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3303 | h3303
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3304 | h3304
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3305 | h3305
                        · linarith only [h3200, h3204, h3205, h3300, h3305, hc12, hc35, hlam, hphi, ht23]
                        · rcases h2bigk with h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h4, hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h2669, hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h2986, hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h0, hlam, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h3198, hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h3200, hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h3202, hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h0, h2986, hc12, hc23, hlam, hphi, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h3302, hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h2986, h3197, h3204, h3205, h3302, h3305, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h3303, hlam, p3307_0]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [h3304, hlam, p3307_1]
                          · have p3307_0 := h3307c.1
                            have p3307_1 := h3307c.2.1
                            have p3307_2 := h3307c.2.2.1
                            have p3307_3 := h3307c.2.2.2
                            linarith only [hlam, p3307_0]
                      · linarith only [h0, h2669, h3195, h3197, h3304, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h3196, h3303, h4, hlam]
                  · linarith only [h3196, h3204, h3205, h3302, h4, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3336 | h3336
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3337 | h3337
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3338 | h3338
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3339 | h3339
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3340 | h3340
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3341 | h3341
                        · rcases h2bigk with h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c | h3342c
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h4, hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h2669, hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h2986, hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h0, hlam, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h3198, hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h3200, hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h3202, hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h0, h2986, hc12, hc23, hlam, hphi, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h3338, hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h0, h2986, h3338, hc12, hc23, hlam, hphi, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h3339, hlam, p3342_0]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [h3340, hlam, p3342_1]
                          · have p3342_0 := h3342c.1
                            have p3342_1 := h3342c.2.1
                            have p3342_2 := h3342c.2.2.1
                            have p3342_3 := h3342c.2.2.2
                            linarith only [hlam, p3342_0]
                        · linarith only [h3197, h3204, h3336, h3341, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h2, h2669, h3337, h3340, hlam]
                    · linarith only [h3204, h3336, h3339, h4, hc03, hc34, hlam, hphi]
                  · linarith only [h3195, h3338, h4, hlam]
                · linarith only [h3204, h3336, h3337, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3373 | h3373
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3374 | h3374
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3375 | h3375
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3376 | h3376
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3377 | h3377
                        · rcases h2bigk with h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h4, hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h2669, hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h2986, hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h0, hlam, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h3198, hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h3200, hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h3202, hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h0, h2986, hc12, hc23, hlam, hphi, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h3374, hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h2986, h3196, h3336, h3374, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h3375, hlam, p3378_0]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [h3376, hlam, p3378_1]
                          · have p3378_0 := h3378c.1
                            have p3378_1 := h3378c.2.1
                            have p3378_2 := h3378c.2.2.1
                            have p3378_3 := h3378c.2.2.2
                            linarith only [hlam, p3378_0]
                        · linarith only [h3204, h3373, h3377, hlam]
                      · linarith only [h0, h2669, h3195, h3204, h3373, h3376, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h3196, h3375, h4, hlam]
                  · linarith only [h3195, h3374, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3408 | h3408
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3409 | h3409
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3410 | h3410
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3411 | h3411
                        · linarith only [h3195, h3198, h3204, h3373, h3411, h4, hc12, hc23, hlam, hphi]
                        · linarith only [h2669, h3197, h3198, h3204, h3411, hc12, hc24, hlam, hphi]
                      · linarith only [h0, h2669, h3195, h3197, h3410, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h3196, h3409, h4, hlam]
                  · linarith only [h3195, h3408, h4, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3417 | h3417
      · linarith only [h0, h3417, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3419 | h3419
        · linarith only [h0, h2669, h3419, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3421 | h3421
          · linarith only [h0, h2986, h3421, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3423 | h3423
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3424 | h3424
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3425 | h3425
                · linarith only [h2, h3197, h3425, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3427 | h3427
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3428 | h3428
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3429 | h3429
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3430 | h3430
                        · linarith only [h1, h3197, h3423, h3430, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h2bigk with h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h2669, h3197, h3429, hc12, hc24, hlam, hphi, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h4, hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h2669, hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h2986, hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h0, hlam, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h3417, hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h3419, hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h3421, hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h3197, h3429, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h2, h3197, h3419, h3429, hc12, hc23, hlam, hphi, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h3427, hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h2, h3197, h3419, h3427, h3429, hc12, hc23, hlam, hphi, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h3428, hlam, p3432_0]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [h3429, hlam, p3432_1]
                          · have p3432_0 := h3432c.1
                            have p3432_1 := h3432c.2.1
                            have p3432_2 := h3432c.2.2.1
                            have p3432_3 := h3432c.2.2.2
                            linarith only [hlam, p3432_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3458 | h3458
                        · linarith only [h0, h2669, h3429, h3458, hc12, hc34, hlam, hphi, ht23]
                        · rcases h2bigk with h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c | h3460c
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h2669, hc12, hc24, hlam, hphi, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h4, hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h2669, hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h2986, hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h0, hlam, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h3417, hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h3419, hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h3421, hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h0, h2986, hc12, hc23, hlam, hphi, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h3427, hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h3429, hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h3428, hlam, p3460_0]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [h2669, h3429, hc04, hc45, hlam, hphi, p3460_1]
                          · have p3460_0 := h3460c.1
                            have p3460_1 := h3460c.2.1
                            have p3460_2 := h3460c.2.2.1
                            have p3460_3 := h3460c.2.2.2
                            linarith only [hlam, p3460_0]
                    · linarith only [h1, h3424, h3428, h4, hlam]
                  · linarith only [h3195, h3427, h4, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3488 | h3488
                · linarith only [h2, h3196, h3197, h3423, h3424, h3488, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3490 | h3490
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3491 | h3491
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3492 | h3492
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3493 | h3493
                        · linarith only [h3196, h3197, h3423, h3424, h3493, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h2bigk with h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h4, hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h2669, hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h2986, hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h0, hlam, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h3417, hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h3419, hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h3421, hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h3196, h3197, h3423, h3424, h3492, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h3490, hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h3196, h3197, h3423, h3424, h3490, h3492, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h3491, hlam, p3495_0]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [h3492, hlam, p3495_1]
                          · have p3495_0 := h3495c.1
                            have p3495_1 := h3495c.2.1
                            have p3495_2 := h3495c.2.2.1
                            have p3495_3 := h3495c.2.2.2
                            linarith only [hlam, p3495_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3521 | h3521
                        · linarith only [h3196, h3423, h3424, h3492, h3521, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · rcases h2bigk with h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h2669, hc12, hc24, hlam, hphi, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h4, hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h2669, hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h2986, hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h0, hlam, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h3417, hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h3419, hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h3421, hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h2, h2669, h3419, hc12, hc23, hlam, hphi, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h2986, h3196, h3423, h3424, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h3490, hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h3492, hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h3491, hlam, p3523_0]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [h3492, hc24, hc45, hlam, hphi, p3523_1]
                          · have p3523_0 := h3523c.1
                            have p3523_1 := h3523c.2.1
                            have p3523_2 := h3523c.2.2.1
                            have p3523_3 := h3523c.2.2.2
                            linarith only [hlam, p3523_0]
                    · linarith only [h3196, h3491, h4, hlam]
                  · linarith only [h1, h3196, h3423, h3424, h3490, h4, hc01, hc15, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3551 | h3551
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3552 | h3552
                · linarith only [h3195, h3197, h3423, h3551, h3552, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h3423, h3551, h3552, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3555 | h3555
                · linarith only [h2, h3197, h3555, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3557 | h3557
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3558 | h3558
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3559 | h3559
                      · linarith only [h3195, h3197, h3417, h3423, h3559, hc12, hc24, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3561 | h3561
                        · linarith only [h0, h2669, h3559, h3561, hc12, hc34, hlam, hphi, ht23]
                        · rcases h2bigk with h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h4, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2669, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2986, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h0, hlam, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h3417, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h3419, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h3421, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2669, h3195, h3423, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h0, h2986, hc12, hc23, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h3557, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h3559, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h3558, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h3559, hc24, hc45, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hlam, p3563_0]
                    · linarith only [h3196, h3558, h4, hlam]
                  · linarith only [h3195, h3557, h4, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3591 | h3591
    · linarith only [h3195, h3196, h3591, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3593 | h3593
      · linarith only [h0, h3593, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3595 | h3595
        · linarith only [h0, h2669, h3595, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3597 | h3597
          · linarith only [h0, h2986, h3597, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3599 | h3599
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3600 | h3600
              · linarith only [h1, h3196, h3600, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3602 | h3602
                · linarith only [h2, h3195, h3196, h3591, h3602, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3604 | h3604
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3605 | h3605
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3606 | h3606
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3607 | h3607
                        · linarith only [h1, h3196, h3591, h3599, h3605, h3607, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases h2bigk with h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h4, hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h2669, hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h2986, hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h0, hlam, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h3593, hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h3595, hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h3597, hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h3196, h3606, h3607, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h1, h3196, h3599, h3606, h3607, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h3604, hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h1, h3196, h3599, h3604, h3606, h3607, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h3605, hlam, p3609_0]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [h3606, hlam, p3609_1]
                          · have p3609_0 := h3609c.1
                            have p3609_1 := h3609c.2.1
                            have p3609_2 := h3609c.2.2.1
                            have p3609_3 := h3609c.2.2.2
                            linarith only [hlam, p3609_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3635 | h3635
                        · linarith only [h3, h3599, h3600, h3606, h3635, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h2bigk with h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h2669, hc12, hc24, hlam, hphi, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h4, hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h2669, hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h2986, hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h0, hlam, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h3593, hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h3595, hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h3597, hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h3196, h3605, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h3604, hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h3606, hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h3606, hc12, hc45, hlam, hphi, ht23, ht34, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h3605, hlam, p3637_0]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [h3606, hc24, hc45, hlam, hphi, p3637_1]
                          · have p3637_0 := h3637c.1
                            have p3637_1 := h3637c.2.1
                            have p3637_2 := h3637c.2.2.1
                            have p3637_3 := h3637c.2.2.2
                            linarith only [hlam, p3637_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3663 | h3663
                      · linarith only [h0, h2669, h3591, h3604, h3605, h3663, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3665 | h3665
                        · linarith only [h0, h1, h2986, h3599, h3605, h3663, h3665, h4, hc12, hc35, hlam, hphi, ht23]
                        · rcases h2bigk with h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c | h3667c
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h2669, h3604, h3605, h3665, hc12, hc45, hlam, hphi, ht23, ht34, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h4, hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h2669, hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h2986, hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h0, hlam, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h3593, hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h3595, hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h3597, hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h3605, h3665, hc02, hc45, hlam, hphi, ht23, ht34, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h3605, h3665, hc12, hc45, hlam, hphi, ht23, ht34, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h3605, h3665, hc24, hc45, hlam, hphi, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h3605, hlam, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h3604, hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h3663, hlam, p3667_0]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h3605, h3665, h4, hc03, hc45, hlam, hphi, ht34, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [h0, h2669, h3605, h3665, hc12, hc45, hlam, hphi, ht23, ht34, p3667_1]
                          · have p3667_0 := h3667c.1
                            have p3667_1 := h3667c.2.1
                            have p3667_2 := h3667c.2.2.1
                            have p3667_3 := h3667c.2.2.2
                            linarith only [hlam, p3667_0]
                  · linarith only [h0, h1, h3599, h3604, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h3195, h3196, h3599, hc13, hc35, hlam, hphi]

end R2N4
