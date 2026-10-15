import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1947 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h3197 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 0 4 5 (by decide) (by decide) with h3198 | h3198
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3199 | h3199
    · linarith only [h0, h3197, h3199, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3201 | h3201
      · linarith only [h0, h1304, h3201, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3203 | h3203
        · linarith only [h0, h1819, h3203, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3205 | h3205
          · linarith only [h1, h1947, h3205, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3207 | h3207
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3208 | h3208
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3209 | h3209
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3210 | h3210
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3211 | h3211
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3212 | h3212
                      · rcases h0bigk with h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [hlam, p3213_0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          rcases p3213_3 (m.d 0 1) (by simp) with h3215 | h3215
                          · rcases p3213_3 (m.d 0 2) (by simp) with h3216 | h3216
                            · linarith only [h0, h3216, hlam]
                            · rcases p3213_3 (m.d 0 3) (by simp) with h3218 | h3218
                              · linarith only [h1, h3218, hlam]
                              · linarith only [h3218, h4, hlam]
                          · linarith only [h0, h3215, hlam]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h1, h3207, h3212, hc45, hlam, hphi, ht0b, ht5b, p3213_1, u0elo0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h2, h3205, h3207, h3212, hc45, hlam, hphi, ht0b, ht5b, p3213_1, u0elo0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          rcases p3213_3 (m.d 0 1) (by simp) with h3224 | h3224
                          · rcases p3213_3 (m.d 0 2) (by simp) with h3225 | h3225
                            · linarith only [h0, h3225, hlam]
                            · rcases p3213_3 (m.d 0 3) (by simp) with h3227 | h3227
                              · linarith only [h1, h3227, hlam]
                              · linarith only [h3197, h3227, hlam]
                          · linarith only [h3, h3224, hlam]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h0, hlam, p3213_0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [hlam, p3213_0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h4, hlam, p3213_0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h1304, hlam, p3213_1]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h1819, hlam, p3213_0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h1, hlam, p3213_1]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h0, h1947, h3209, hc12, hc23, hlam, hphi, p3213_1]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [hlam, p3213_0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h1947, hlam, p3213_1]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h0, h1819, h1947, h3209, hc12, hc23, hlam, hphi, p3213_1]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h2, hlam, p3213_0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h0, h1947, h3209, hc12, hc23, hlam, hphi, p3213_1]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h1, h1947, h3207, h3209, h3212, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3213_1]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [hlam, p3213_0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h0, h1819, h1947, h3209, hc12, hc23, hlam, hphi, p3213_1]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h3, hlam, p3213_0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h0, h1947, h3197, h3209, hc12, hc23, hlam, hphi, p3213_1]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h3197, hlam, p3213_0]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [h3198, hlam, p3213_1]
                        · have p3213_0 := h3213c.1
                          have p3213_1 := h3213c.2.1
                          have p3213_2 := h3213c.2.2.1
                          have p3213_3 := h3213c.2.2.2
                          linarith only [hlam, p3213_0]
                      · linarith only [h1947, h3198, h3212, hlam]
                    · linarith only [h1947, h2, h3208, h3209, h3211, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1, h1947, h3207, h3210, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3254 | h3254
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3255 | h3255
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3256 | h3256
                      · rcases h0bigk with h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [hlam, p3257_0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          rcases p3257_3 (m.d 0 1) (by simp) with h3259 | h3259
                          · rcases p3257_3 (m.d 0 2) (by simp) with h3260 | h3260
                            · linarith only [h0, h3260, hlam]
                            · rcases p3257_3 (m.d 0 3) (by simp) with h3262 | h3262
                              · linarith only [h1, h3262, hlam]
                              · linarith only [h3262, h4, hlam]
                          · linarith only [h0, h3259, hlam]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h1, h3207, hc35, hlam, hphi, ht0b, ht5b, p3257_1, u0elo0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h1, h1947, h3207, hc35, hlam, hphi, ht0b, ht5b, p3257_1, u0elo0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          rcases p3257_3 (m.d 0 1) (by simp) with h3268 | h3268
                          · rcases p3257_3 (m.d 0 2) (by simp) with h3269 | h3269
                            · linarith only [h0, h3269, hlam]
                            · rcases p3257_3 (m.d 0 3) (by simp) with h3271 | h3271
                              · linarith only [h1, h3271, hlam]
                              · linarith only [h3197, h3271, hlam]
                          · linarith only [h3, h3268, hlam]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h0, hlam, p3257_0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [hlam, p3257_0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h4, hlam, p3257_0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h1304, hlam, p3257_1]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h1819, hlam, p3257_0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h1, hlam, p3257_1]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h0, h3209, h4, hc12, hc34, hlam, hphi, ht23, p3257_1]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [hlam, p3257_0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h1947, hlam, p3257_1]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h0, h1819, h3209, h4, hc12, hc34, hlam, hphi, ht23, p3257_1]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h2, hlam, p3257_0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          rcases p3257_3 (m.d 0 1) (by simp) with h3286 | h3286
                          · rcases p3257_3 (m.d 0 2) (by simp) with h3287 | h3287
                            · linarith only [h1304, h3287, hlam]
                            · rcases p3257_3 (m.d 0 3) (by simp) with h3289 | h3289
                              · linarith only [h1947, h3289, hlam]
                              · linarith only [h3289, h4, hlam]
                          · linarith only [h0, h3286, hlam]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h1, h3207, h3256, hc45, hlam, hphi, ht0b, ht5b, p3257_1, u0elo3]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [hlam, p3257_0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          rcases p3257_3 (m.d 0 1) (by simp) with h3295 | h3295
                          · rcases p3257_3 (m.d 0 2) (by simp) with h3296 | h3296
                            · linarith only [h1304, h3296, hlam]
                            · rcases p3257_3 (m.d 0 3) (by simp) with h3298 | h3298
                              · linarith only [h1947, h3298, hlam]
                              · linarith only [h3197, h3298, hlam]
                          · linarith only [h3, h3295, hlam]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h3, hlam, p3257_0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h0, h3197, h3209, h4, hc12, hc34, hlam, hphi, ht23, p3257_1]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h3197, hlam, p3257_0]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [h3198, hlam, p3257_1]
                        · have p3257_0 := h3257c.1
                          have p3257_1 := h3257c.2.1
                          have p3257_2 := h3257c.2.2.1
                          have p3257_3 := h3257c.2.2.2
                          linarith only [hlam, p3257_0]
                      · linarith only [h0, h3209, h3256, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1304, h3198, h3255, hlam]
                  · linarith only [h1, h3207, h3254, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h2, h3198, h3205, h3207, h3208, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
            · linarith only [h1947, h3197, h3207, hc13, hc34, hlam, hphi]
  · linarith only [h1947, h3197, h3198, hlam]

end R2N4
