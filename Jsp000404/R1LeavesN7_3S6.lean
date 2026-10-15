import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S3
import Jsp000404.R1LeavesN7_3S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1951 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2201 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2272 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h3327 | h3327
  · rcases m.htr 1 4 5 (by decide) (by decide) with h3328 | h3328
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3329 | h3329
      · linarith only [h0, h2272, h3327, h3329, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3331 | h3331
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3332 | h3332
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3333 | h3333
            · rcases h1bigk with h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h0, h2201, h3329, h3331, h4, h7, hlam, p3334_2]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                rcases p3334_3 (m.d 0 1) (by simp) with h3337 | h3337
                · rcases p3334_3 (m.d 1 2) (by simp) with h3338 | h3338
                  · linarith only [h0, h3338, hlam]
                  · rcases p3334_3 (m.d 1 3) (by simp) with h3340 | h3340
                    · linarith only [h3340, hlam, p3334_0]
                    · rcases p3334_3 (m.d 1 4) (by simp) with h3342 | h3342
                      · linarith only [h2, h3342, hlam]
                      · linarith only [h2272, h3342, hlam]
                · linarith only [h3337, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                rcases p3334_3 (m.d 0 1) (by simp) with h3346 | h3346
                · rcases p3334_3 (m.d 1 2) (by simp) with h3347 | h3347
                  · linarith only [h0, h3347, hlam]
                  · rcases p3334_3 (m.d 1 3) (by simp) with h3349 | h3349
                    · linarith only [h1, h3349, hlam]
                    · rcases p3334_3 (m.d 1 4) (by simp) with h3351 | h3351
                      · linarith only [h3351, hlam, p3334_0]
                      · rcases p3334_3 (m.d 1 5) (by simp) with h3353 | h3353
                        · linarith only [h3, h3353, hlam]
                        · rcases h3bigk with h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            rcases p3355_3 (m.d 0 3) (by simp) with h3357 | h3357
                            · rcases p3355_3 (m.d 1 3) (by simp) with h3358 | h3358
                              · linarith only [h1, h3358, hlam]
                              · rcases p3355_3 (m.d 2 3) (by simp) with h3360 | h3360
                                · linarith only [h3360, h4, hlam]
                                · linarith only [h10, h3360, hlam]
                            · linarith only [h1, h3357, hlam]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            rcases p3355_3 (m.d 0 3) (by simp) with h3364 | h3364
                            · rcases p3355_3 (m.d 1 3) (by simp) with h3365 | h3365
                              · linarith only [h1, h3365, hlam]
                              · rcases p3355_3 (m.d 2 3) (by simp) with h3367 | h3367
                                · linarith only [h3367, h4, hlam]
                                · rcases p3355_3 (m.d 3 4) (by simp) with h3369 | h3369
                                  · linarith only [h3369, h7, hlam]
                                  · linarith only [h3329, h3369, hlam]
                            · linarith only [h3364, h4, hlam]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h0, h2201, h3329, h3331, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3355_1]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h10, h3327, h3329, h7, hlam, p3355_2]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h1, hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h10, hlam, p3355_1]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h2272, hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h2272, hc01, hc35, hlam, hphi, ht0b, ht5b, p3334_1, p3355_1]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h4, hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h3329, h7, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3355_1]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h3329, hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h0, h3329, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p3355_1]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h7, hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h0, h3327, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p3355_1]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3355_1]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            rcases p3355_3 (m.d 0 3) (by simp) with h3389 | h3389
                            · rcases p3355_3 (m.d 1 3) (by simp) with h3390 | h3390
                              · linarith only [h2272, h3390, hlam]
                              · linarith only [h3327, h3390, hlam]
                            · linarith only [h3389, h8, hlam]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h8, hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h3327, hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h3331, hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [h3333, hlam, p3355_0]
                          · have p3355_0 := h3355c.1
                            have p3355_1 := h3355c.2.1
                            have p3355_2 := h3355c.2.2.1
                            have p3355_3 := h3355c.2.2.2
                            linarith only [hlam, p3355_0]
                · linarith only [h3346, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                rcases p3334_3 (m.d 0 1) (by simp) with h3400 | h3400
                · rcases p3334_3 (m.d 1 2) (by simp) with h3401 | h3401
                  · linarith only [h0, h3401, hlam]
                  · rcases p3334_3 (m.d 1 3) (by simp) with h3403 | h3403
                    · linarith only [h1, h3403, hlam]
                    · linarith only [h3327, h3403, hlam]
                · linarith only [h3400, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h0, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h10, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h1951, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h2201, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h1, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h0, h2272, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3334_1]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h2272, hlam, p3334_1]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h0, h2272, h4, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p3334_1]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h2, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                rcases p3334_3 (m.d 0 1) (by simp) with h3418 | h3418
                · rcases p3334_3 (m.d 1 2) (by simp) with h3419 | h3419
                  · linarith only [h1951, h3419, hlam]
                  · rcases p3334_3 (m.d 1 3) (by simp) with h3421 | h3421
                    · linarith only [h2272, h3421, hlam]
                    · linarith only [h10, h3421, hlam]
                · linarith only [h0, h3418, hlam]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h2, h3327, h3333, hc01, hc45, hlam, hphi, ht0b, ht5b, p3334_1]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                rcases p3334_3 (m.d 0 1) (by simp) with h3427 | h3427
                · rcases p3334_3 (m.d 1 2) (by simp) with h3428 | h3428
                  · linarith only [h1951, h3428, hlam]
                  · rcases p3334_3 (m.d 1 3) (by simp) with h3430 | h3430
                    · linarith only [h2272, h3430, hlam]
                    · linarith only [h3327, h3430, hlam]
                · linarith only [h3, h3427, hlam]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h3, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h0, h10, h3327, h3329, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3334_1]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h3327, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [h3328, hlam, p3334_0]
              · have p3334_0 := h3334c.1
                have p3334_1 := h3334c.2.1
                have p3334_2 := h3334c.2.2.1
                have p3334_3 := h3334c.2.2.2
                linarith only [hlam, p3334_0]
            · linarith only [h0, h10, h3329, h3333, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h10, h1951, h3327, h3328, h3329, h3332, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h10, h3327, h3331, hlam]
    · linarith only [h2272, h3327, h3328, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h3443 | h3443
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3444 | h3444
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3445 | h3445
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3446 | h3446
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3447 | h3447
            · rcases h1bigk with h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c | h3448c
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h0, h10, h3327, h3444, h3447, h4, hlam, p3448_2]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h0, h3327, h3444, h3447, h4, hlam, p3448_2]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                rcases p3448_3 (m.d 0 1) (by simp) with h3452 | h3452
                · rcases p3448_3 (m.d 1 2) (by simp) with h3453 | h3453
                  · linarith only [h0, h3453, hlam]
                  · rcases p3448_3 (m.d 1 3) (by simp) with h3455 | h3455
                    · linarith only [h1, h3455, hlam]
                    · rcases p3448_3 (m.d 1 4) (by simp) with h3457 | h3457
                      · linarith only [h3457, hlam, p3448_0]
                      · rcases p3448_3 (m.d 1 5) (by simp) with h3459 | h3459
                        · linarith only [h3, h3459, hlam]
                        · rcases h3bigk with h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c | h3461c
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            rcases p3461_3 (m.d 0 3) (by simp) with h3463 | h3463
                            · rcases p3461_3 (m.d 1 3) (by simp) with h3464 | h3464
                              · linarith only [h1, h3464, hlam]
                              · rcases p3461_3 (m.d 2 3) (by simp) with h3466 | h3466
                                · linarith only [h3466, h4, hlam]
                                · linarith only [h10, h3466, hlam]
                            · linarith only [h1, h3463, hlam]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h10, h3327, h3444, h3447, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3461_1]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            rcases p3461_3 (m.d 0 3) (by simp) with h3471 | h3471
                            · rcases p3461_3 (m.d 1 3) (by simp) with h3472 | h3472
                              · linarith only [h1, h3472, hlam]
                              · rcases p3461_3 (m.d 2 3) (by simp) with h3474 | h3474
                                · linarith only [h3474, h4, hlam]
                                · linarith only [h3444, h3474, hlam]
                            · linarith only [h3471, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            rcases p3461_3 (m.d 0 3) (by simp) with h3478 | h3478
                            · rcases p3461_3 (m.d 1 3) (by simp) with h3479 | h3479
                              · linarith only [h1, h3479, hlam]
                              · rcases p3461_3 (m.d 2 3) (by simp) with h3481 | h3481
                                · linarith only [h3481, h4, hlam]
                                · linarith only [h3445, h3481, hlam]
                            · linarith only [h3478, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h1, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h10, hlam, p3461_1]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h2272, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h3327, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h4, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            rcases p3461_3 (m.d 0 3) (by simp) with h3491 | h3491
                            · rcases p3461_3 (m.d 1 3) (by simp) with h3492 | h3492
                              · linarith only [h10, h3492, hlam]
                              · rcases p3461_3 (m.d 2 3) (by simp) with h3494 | h3494
                                · rcases p3461_3 (m.d 3 4) (by simp) with h3495 | h3495
                                  · linarith only [h3444, h3495, hlam]
                                  · linarith only [h2272, h3495, hlam]
                                · linarith only [h10, h3494, hlam]
                            · linarith only [h1, h3491, hlam]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h10, h3327, h3447, hc12, hc23, hlam, hphi, p3461_1]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h0, h10, h3327, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3461_1]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h7, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h0, h10, h3444, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3461_1]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h3444, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h10, h3327, h3444, hc12, hc24, hlam, hphi, p3461_1]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h8, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h0, h10, h3445, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3461_1]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h3445, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [h3447, hlam, p3461_0]
                          · have p3461_0 := h3461c.1
                            have p3461_1 := h3461c.2.1
                            have p3461_2 := h3461c.2.2.1
                            have p3461_3 := h3461c.2.2.2
                            linarith only [hlam, p3461_0]
                · linarith only [h3452, hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                rcases p3448_3 (m.d 0 1) (by simp) with h3514 | h3514
                · rcases p3448_3 (m.d 1 2) (by simp) with h3515 | h3515
                  · linarith only [h0, h3515, hlam]
                  · rcases p3448_3 (m.d 1 3) (by simp) with h3517 | h3517
                    · linarith only [h1, h3517, hlam]
                    · rcases p3448_3 (m.d 1 4) (by simp) with h3519 | h3519
                      · linarith only [h2, h3519, hlam]
                      · linarith only [h3443, h3519, hlam]
                · linarith only [h3514, hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h0, hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h10, hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h1951, hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h2201, hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h1, hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h0, h2272, h3444, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3448_1]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h2272, hlam, p3448_1]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h3327, hlam, p3448_1]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h2, hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h0, h2272, h3444, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3448_1]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h0, h2272, h3444, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3448_1]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h0, h2272, h3444, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p3448_1]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h3, hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h0, h3327, h3444, h3447, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3448_1]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h0, h10, h3327, h3444, h3447, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3448_1]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [h3443, hlam, p3448_0]
              · have p3448_0 := h3448c.1
                have p3448_1 := h3448c.2.1
                have p3448_2 := h3448c.2.2.1
                have p3448_3 := h3448c.2.2.2
                linarith only [hlam, p3448_0]
            · linarith only [h2272, h3443, h3447, hlam]
          · linarith only [h1951, h2272, h3443, h3446, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h0, h2272, h3443, h3444, h3445, h4, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3546 | h3546
        · linarith only [h10, h3327, h3444, h3546, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3548 | h3548
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3549 | h3549
            · rcases h1bigk with h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h0, h10, h3546, h3549, h4, h7, hlam, p3550_2]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                rcases p3550_3 (m.d 0 1) (by simp) with h3553 | h3553
                · rcases p3550_3 (m.d 1 2) (by simp) with h3554 | h3554
                  · linarith only [h0, h3554, hlam]
                  · rcases p3550_3 (m.d 1 3) (by simp) with h3556 | h3556
                    · linarith only [h3556, hlam, p3550_0]
                    · rcases p3550_3 (m.d 1 4) (by simp) with h3558 | h3558
                      · linarith only [h2, h3558, hlam]
                      · linarith only [h2272, h3558, hlam]
                · linarith only [h3553, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                rcases p3550_3 (m.d 0 1) (by simp) with h3562 | h3562
                · rcases p3550_3 (m.d 1 2) (by simp) with h3563 | h3563
                  · linarith only [h0, h3563, hlam]
                  · rcases p3550_3 (m.d 1 3) (by simp) with h3565 | h3565
                    · linarith only [h1, h3565, hlam]
                    · rcases p3550_3 (m.d 1 4) (by simp) with h3567 | h3567
                      · linarith only [h3567, hlam, p3550_0]
                      · rcases p3550_3 (m.d 1 5) (by simp) with h3569 | h3569
                        · linarith only [h3, h3569, hlam]
                        · rcases h3bigk with h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c | h3571c
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            rcases p3571_3 (m.d 0 3) (by simp) with h3573 | h3573
                            · rcases p3571_3 (m.d 1 3) (by simp) with h3574 | h3574
                              · linarith only [h1, h3574, hlam]
                              · rcases p3571_3 (m.d 2 3) (by simp) with h3576 | h3576
                                · linarith only [h3576, h4, hlam]
                                · linarith only [h10, h3576, hlam]
                            · linarith only [h1, h3573, hlam]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            rcases p3571_3 (m.d 0 3) (by simp) with h3580 | h3580
                            · rcases p3571_3 (m.d 1 3) (by simp) with h3581 | h3581
                              · linarith only [h1, h3581, hlam]
                              · rcases p3571_3 (m.d 2 3) (by simp) with h3583 | h3583
                                · linarith only [h3583, h4, hlam]
                                · rcases p3571_3 (m.d 3 4) (by simp) with h3585 | h3585
                                  · linarith only [h3585, h7, hlam]
                                  · linarith only [h3444, h3585, hlam]
                            · linarith only [h3580, h4, hlam]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h0, h10, h3546, h3549, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3571_1]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h0, h10, h3546, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3571_1]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h1, hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h10, hlam, p3571_1]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h2272, hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h3327, hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h4, hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h3546, h3549, hc13, hc34, hlam, hphi, p3571_1]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h3444, hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h3546, hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h7, hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            rcases p3571_3 (m.d 0 3) (by simp) with h3602 | h3602
                            · rcases p3571_3 (m.d 1 3) (by simp) with h3603 | h3603
                              · linarith only [h3603, hlam, p3571_0]
                              · rcases p3571_3 (m.d 2 3) (by simp) with h3605 | h3605
                                · linarith only [h3444, h3605, hlam]
                                · linarith only [h10, h3605, hlam]
                            · linarith only [h1, h3602, hlam]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3571_1]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h0, h10, h3327, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3571_1]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h8, hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            rcases p3571_3 (m.d 0 3) (by simp) with h3613 | h3613
                            · rcases p3571_3 (m.d 1 3) (by simp) with h3614 | h3614
                              · linarith only [h3614, hlam, p3571_0]
                              · rcases p3571_3 (m.d 2 3) (by simp) with h3616 | h3616
                                · linarith only [h3546, h3616, hlam]
                                · linarith only [h10, h3616, hlam]
                            · linarith only [h1, h3613, hlam]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h10, hc12, hc35, hlam, hphi, ht23, p3571_1]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [h3549, hlam, p3571_0]
                          · have p3571_0 := h3571c.1
                            have p3571_1 := h3571c.2.1
                            have p3571_2 := h3571c.2.2.1
                            have p3571_3 := h3571c.2.2.2
                            linarith only [hlam, p3571_0]
                · linarith only [h3562, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                rcases p3550_3 (m.d 0 1) (by simp) with h3624 | h3624
                · rcases p3550_3 (m.d 1 2) (by simp) with h3625 | h3625
                  · linarith only [h0, h3625, hlam]
                  · rcases p3550_3 (m.d 1 3) (by simp) with h3627 | h3627
                    · linarith only [h1, h3627, hlam]
                    · rcases p3550_3 (m.d 1 4) (by simp) with h3629 | h3629
                      · linarith only [h2, h3629, hlam]
                      · linarith only [h3443, h3629, hlam]
                · linarith only [h3624, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h0, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h10, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h1951, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h2201, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h1, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h0, h2272, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3550_1]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h2272, hlam, p3550_1]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h3327, hlam, p3550_1]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h2, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                rcases p3550_3 (m.d 0 1) (by simp) with h3644 | h3644
                · rcases p3550_3 (m.d 1 2) (by simp) with h3645 | h3645
                  · linarith only [h1951, h3645, hlam]
                  · rcases p3550_3 (m.d 1 3) (by simp) with h3647 | h3647
                    · linarith only [h2272, h3647, hlam]
                    · linarith only [h10, h3647, hlam]
                · linarith only [h0, h3644, hlam]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                rcases p3550_3 (m.d 0 1) (by simp) with h3651 | h3651
                · rcases p3550_3 (m.d 1 2) (by simp) with h3652 | h3652
                  · linarith only [h1951, h3652, hlam]
                  · rcases p3550_3 (m.d 1 3) (by simp) with h3654 | h3654
                    · linarith only [h2272, h3654, hlam]
                    · rcases p3550_3 (m.d 1 4) (by simp) with h3656 | h3656
                      · rcases p3550_3 (m.d 1 5) (by simp) with h3657 | h3657
                        · linarith only [h3443, h3657, hlam]
                        · linarith only [h3327, h3657, hlam]
                      · linarith only [h2272, h3656, hlam]
                · linarith only [h1, h3651, hlam]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                rcases p3550_3 (m.d 0 1) (by simp) with h3663 | h3663
                · rcases p3550_3 (m.d 1 2) (by simp) with h3664 | h3664
                  · linarith only [h1951, h3664, hlam]
                  · rcases p3550_3 (m.d 1 3) (by simp) with h3666 | h3666
                    · linarith only [h2272, h3666, hlam]
                    · rcases p3550_3 (m.d 1 4) (by simp) with h3668 | h3668
                      · rcases p3550_3 (m.d 1 5) (by simp) with h3669 | h3669
                        · linarith only [h3443, h3669, hlam]
                        · rcases h3bigk with h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c | h3671c
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h2272, h3327, h7, hlam, p3550_1, p3671_2]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            rcases p3671_3 (m.d 0 3) (by simp) with h3674 | h3674
                            · rcases p3671_3 (m.d 1 3) (by simp) with h3675 | h3675
                              · linarith only [h1, h3675, hlam]
                              · rcases p3671_3 (m.d 2 3) (by simp) with h3677 | h3677
                                · linarith only [h3677, h4, hlam]
                                · rcases p3671_3 (m.d 3 4) (by simp) with h3679 | h3679
                                  · linarith only [h3679, h7, hlam]
                                  · linarith only [h3444, h3679, hlam]
                            · linarith only [h3674, h4, hlam]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h0, h1951, h3327, h3444, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3550_1, p3671_1]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h0, h10, h3546, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3671_1]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h1, hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h10, hlam, p3671_1]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h2272, hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h3327, hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h4, hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h3546, hc13, hc35, hlam, hphi, p3671_1]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h3444, hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h3546, hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h7, hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            rcases p3671_3 (m.d 0 3) (by simp) with h3696 | h3696
                            · rcases p3671_3 (m.d 1 3) (by simp) with h3697 | h3697
                              · linarith only [h3697, hlam, p3671_0]
                              · rcases p3671_3 (m.d 2 3) (by simp) with h3699 | h3699
                                · linarith only [h3444, h3699, hlam]
                                · linarith only [h10, h3699, hlam]
                            · linarith only [h1, h3696, hlam]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3671_1]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h0, h10, h3327, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3671_1]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h8, hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            rcases p3671_3 (m.d 0 3) (by simp) with h3707 | h3707
                            · rcases p3671_3 (m.d 1 3) (by simp) with h3708 | h3708
                              · linarith only [h3708, hlam, p3671_0]
                              · rcases p3671_3 (m.d 2 3) (by simp) with h3710 | h3710
                                · linarith only [h3546, h3710, hlam]
                                · linarith only [h10, h3710, hlam]
                            · linarith only [h1, h3707, hlam]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h10, hc12, hc35, hlam, hphi, ht23, p3671_1]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [h3549, hlam, p3671_0]
                          · have p3671_0 := h3671c.1
                            have p3671_1 := h3671c.2.1
                            have p3671_2 := h3671c.2.2.1
                            have p3671_3 := h3671c.2.2.2
                            linarith only [hlam, p3671_0]
                      · linarith only [h3443, h3668, hlam]
                · linarith only [h3, h3663, hlam]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h3, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                rcases p3550_3 (m.d 0 1) (by simp) with h3720 | h3720
                · rcases p3550_3 (m.d 1 2) (by simp) with h3721 | h3721
                  · linarith only [h2201, h3721, hlam]
                  · rcases p3550_3 (m.d 1 3) (by simp) with h3723 | h3723
                    · linarith only [h3327, h3723, hlam]
                    · linarith only [h10, h3723, hlam]
                · linarith only [h0, h3720, hlam]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                rcases p3550_3 (m.d 0 1) (by simp) with h3727 | h3727
                · rcases p3550_3 (m.d 1 2) (by simp) with h3728 | h3728
                  · linarith only [h2201, h3728, hlam]
                  · rcases p3550_3 (m.d 1 3) (by simp) with h3730 | h3730
                    · linarith only [h3327, h3730, hlam]
                    · rcases p3550_3 (m.d 1 4) (by simp) with h3732 | h3732
                      · rcases p3550_3 (m.d 1 5) (by simp) with h3733 | h3733
                        · rcases h3bigk with h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h3327, h3549, h7, hlam, p3550_1, p3734_2]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            rcases p3734_3 (m.d 0 3) (by simp) with h3737 | h3737
                            · rcases p3734_3 (m.d 1 3) (by simp) with h3738 | h3738
                              · linarith only [h1, h3738, hlam]
                              · rcases p3734_3 (m.d 2 3) (by simp) with h3740 | h3740
                                · linarith only [h3740, h4, hlam]
                                · rcases p3734_3 (m.d 3 4) (by simp) with h3742 | h3742
                                  · linarith only [h3742, h7, hlam]
                                  · linarith only [h3444, h3742, hlam]
                            · linarith only [h3737, h4, hlam]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h0, h1951, h3443, h3444, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3550_1, p3734_1]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h0, h10, h2201, h3546, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3550_1, p3734_1]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h1, hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h10, hlam, p3734_1]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h2272, hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h3327, hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h4, hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h10, h3444, hc12, hc34, hlam, hphi, ht23, p3734_1]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h3444, hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h3546, hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h7, hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            rcases p3734_3 (m.d 0 3) (by simp) with h3759 | h3759
                            · rcases p3734_3 (m.d 1 3) (by simp) with h3760 | h3760
                              · linarith only [h3760, hlam, p3734_0]
                              · rcases p3734_3 (m.d 2 3) (by simp) with h3762 | h3762
                                · linarith only [h3444, h3762, hlam]
                                · linarith only [h10, h3762, hlam]
                            · linarith only [h1, h3759, hlam]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3734_1]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h0, h10, h2201, h3546, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3550_1, p3734_1]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h8, hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            rcases p3734_3 (m.d 0 3) (by simp) with h3770 | h3770
                            · rcases p3734_3 (m.d 1 3) (by simp) with h3771 | h3771
                              · linarith only [h3771, hlam, p3734_0]
                              · rcases p3734_3 (m.d 2 3) (by simp) with h3773 | h3773
                                · linarith only [h3546, h3773, hlam]
                                · linarith only [h10, h3773, hlam]
                            · linarith only [h1, h3770, hlam]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h10, hc12, hc35, hlam, hphi, ht23, p3734_1]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [h3549, hlam, p3734_0]
                          · have p3734_0 := h3734c.1
                            have p3734_1 := h3734c.2.1
                            have p3734_2 := h3734c.2.2.1
                            have p3734_3 := h3734c.2.2.2
                            linarith only [hlam, p3734_0]
                        · linarith only [h3327, h3733, hlam]
                      · linarith only [h2272, h3732, hlam]
                · linarith only [h1, h3727, hlam]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [h3443, hlam, p3550_0]
              · have p3550_0 := h3550c.1
                have p3550_1 := h3550c.2.1
                have p3550_2 := h3550c.2.2.1
                have p3550_3 := h3550c.2.2.2
                linarith only [hlam, p3550_0]
            · linarith only [h2272, h3443, h3549, hlam]
          · linarith only [h1951, h3443, h3548, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3787 | h3787
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3788 | h3788
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3789 | h3789
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3790 | h3790
            · linarith only [h10, h2272, h3443, h3787, h3790, hc12, hc23, hlam, hphi]
            · linarith only [h10, h2272, h3789, h3790, hc12, hc24, hlam, hphi]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3793 | h3793
            · linarith only [h0, h1951, h3789, h3793, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h0, h10, h2272, h3787, h3789, h4, h7, h9, hlam, p3795_2]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h0, h2272, h3787, h3789, h4, h7, h9, hlam, p3795_2]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                rcases p3795_3 (m.d 0 1) (by simp) with h3799 | h3799
                · rcases p3795_3 (m.d 1 2) (by simp) with h3800 | h3800
                  · linarith only [h0, h3800, hlam]
                  · rcases p3795_3 (m.d 1 3) (by simp) with h3802 | h3802
                    · linarith only [h1, h3802, hlam]
                    · rcases p3795_3 (m.d 1 4) (by simp) with h3804 | h3804
                      · linarith only [h3804, hlam, p3795_0]
                      · rcases p3795_3 (m.d 1 5) (by simp) with h3806 | h3806
                        · linarith only [h3, h3806, hlam]
                        · linarith only [h3443, h3806, hlam]
                · linarith only [h3799, hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                rcases p3795_3 (m.d 0 1) (by simp) with h3810 | h3810
                · rcases p3795_3 (m.d 1 2) (by simp) with h3811 | h3811
                  · linarith only [h0, h3811, hlam]
                  · rcases p3795_3 (m.d 1 3) (by simp) with h3813 | h3813
                    · linarith only [h1, h3813, hlam]
                    · rcases p3795_3 (m.d 1 4) (by simp) with h3815 | h3815
                      · linarith only [h2, h3815, hlam]
                      · rcases p3795_3 (m.d 1 5) (by simp) with h3817 | h3817
                        · linarith only [h3817, hlam, p3795_0]
                        · rcases h3bigk with h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h2272, h3787, h3789, h7, h9, hlam, p3819_2]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h0, h3327, h3788, h4, hlam, p3795_2, p3819_1]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            rcases p3819_3 (m.d 0 3) (by simp) with h3823 | h3823
                            · rcases p3819_3 (m.d 1 3) (by simp) with h3824 | h3824
                              · linarith only [h1, h3824, hlam]
                              · rcases p3819_3 (m.d 2 3) (by simp) with h3826 | h3826
                                · linarith only [h3826, h4, hlam]
                                · linarith only [h3787, h3826, hlam]
                            · linarith only [h3823, hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            rcases p3819_3 (m.d 0 3) (by simp) with h3830 | h3830
                            · rcases p3819_3 (m.d 1 3) (by simp) with h3831 | h3831
                              · linarith only [h1, h3831, hlam]
                              · rcases p3819_3 (m.d 2 3) (by simp) with h3833 | h3833
                                · linarith only [h3833, h4, hlam]
                                · linarith only [h3788, h3833, hlam]
                            · linarith only [h3830, hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h1, hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h10, hlam, p3819_1]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h2272, hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h3327, hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h4, hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            rcases p3819_3 (m.d 0 3) (by simp) with h3843 | h3843
                            · rcases p3819_3 (m.d 1 3) (by simp) with h3844 | h3844
                              · linarith only [h10, h3844, hlam]
                              · rcases p3819_3 (m.d 2 3) (by simp) with h3846 | h3846
                                · rcases p3819_3 (m.d 3 4) (by simp) with h3847 | h3847
                                  · linarith only [h3787, h3847, hlam]
                                  · linarith only [h2272, h3847, hlam]
                                · linarith only [h10, h3846, hlam]
                            · linarith only [h1, h3843, hlam]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h10, h2272, hc12, hc23, hlam, hphi, p3819_1]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h0, h10, h2272, h3793, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3819_1]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h7, hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h0, h10, h3787, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3819_1]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h3787, hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h3793, hlam, p3819_1]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h8, hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h0, h10, h3788, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3819_1]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h3788, hlam, p3819_0]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [h10, h2272, h3788, hc12, hc25, hlam, hphi, p3819_1]
                          · have p3819_0 := h3819c.1
                            have p3819_1 := h3819c.2.1
                            have p3819_2 := h3819c.2.2.1
                            have p3819_3 := h3819c.2.2.2
                            linarith only [hlam, p3819_0]
                · linarith only [h3810, hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h0, hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h10, hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h1951, hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h2201, hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h1, hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h2272, hc12, hc34, hlam, hphi, ht23, p3795_1]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h2272, hlam, p3795_1]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h3327, hlam, p3795_1]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h2, hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h0, h1951, h3789, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3795_1]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h0, h1951, h3789, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3795_1]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h3443, hlam, p3795_1]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h3, hlam, p3795_0]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h0, h3327, h3788, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3795_1]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h0, h10, h3327, h3788, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3795_1]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [h0, h3327, h3788, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3795_1]
              · have p3795_0 := h3795c.1
                have p3795_1 := h3795c.2.1
                have p3795_2 := h3795c.2.2.1
                have p3795_3 := h3795c.2.2.2
                linarith only [hlam, p3795_0]
        · linarith only [h10, h2272, h3787, h3788, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3887 | h3887
        · linarith only [h0, h10, h3327, h3787, h3887, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3889 | h3889
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3890 | h3890
            · rcases h1bigk with h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h0, h10, h3887, h3890, h4, h7, hlam, p3891_2]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h0, h2272, h3443, h3787, h3889, h4, h7, hlam, p3891_2]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h0, h3443, h3787, h3889, h4, h7, hlam, p3891_2]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                rcases p3891_3 (m.d 0 1) (by simp) with h3896 | h3896
                · rcases p3891_3 (m.d 1 2) (by simp) with h3897 | h3897
                  · linarith only [h0, h3897, hlam]
                  · rcases p3891_3 (m.d 1 3) (by simp) with h3899 | h3899
                    · linarith only [h1, h3899, hlam]
                    · rcases p3891_3 (m.d 1 4) (by simp) with h3901 | h3901
                      · linarith only [h2, h3901, hlam]
                      · rcases p3891_3 (m.d 1 5) (by simp) with h3903 | h3903
                        · linarith only [h3903, hlam, p3891_0]
                        · rcases h3bigk with h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h2272, h3443, h3787, h3889, h7, hlam, p3905_2]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            rcases p3905_3 (m.d 0 3) (by simp) with h3908 | h3908
                            · rcases p3905_3 (m.d 1 3) (by simp) with h3909 | h3909
                              · linarith only [h1, h3909, hlam]
                              · rcases p3905_3 (m.d 2 3) (by simp) with h3911 | h3911
                                · linarith only [h3911, h4, hlam]
                                · rcases p3905_3 (m.d 3 4) (by simp) with h3913 | h3913
                                  · linarith only [h3913, h7, hlam]
                                  · linarith only [h3787, h3913, hlam]
                            · linarith only [h3908, h4, hlam]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h0, h10, h2272, h3443, h3787, h3889, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3905_1]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h0, h10, h3887, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3905_1]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h1, hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h10, hlam, p3905_1]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h2272, hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h3327, hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h4, hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h10, h3887, hc12, hc35, hlam, hphi, ht23, p3905_1]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h3787, hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h3887, hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h7, hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            rcases p3905_3 (m.d 0 3) (by simp) with h3930 | h3930
                            · rcases p3905_3 (m.d 1 3) (by simp) with h3931 | h3931
                              · linarith only [h3931, hlam, p3905_0]
                              · rcases p3905_3 (m.d 2 3) (by simp) with h3933 | h3933
                                · linarith only [h3787, h3933, hlam]
                                · linarith only [h10, h3933, hlam]
                            · linarith only [h1, h3930, hlam]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h10, hc12, hc34, hlam, hphi, ht23, p3905_1]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h0, h10, h3327, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3905_1]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h8, hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            rcases p3905_3 (m.d 0 3) (by simp) with h3941 | h3941
                            · rcases p3905_3 (m.d 1 3) (by simp) with h3942 | h3942
                              · linarith only [h3942, hlam, p3905_0]
                              · rcases p3905_3 (m.d 2 3) (by simp) with h3944 | h3944
                                · linarith only [h3887, h3944, hlam]
                                · linarith only [h10, h3944, hlam]
                            · linarith only [h1, h3941, hlam]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h10, hc12, hc35, hlam, hphi, ht23, p3905_1]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [h3890, hlam, p3905_0]
                          · have p3905_0 := h3905c.1
                            have p3905_1 := h3905c.2.1
                            have p3905_2 := h3905c.2.2.1
                            have p3905_3 := h3905c.2.2.2
                            linarith only [hlam, p3905_0]
                · linarith only [h3896, hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h0, hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h10, hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h1951, hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h2201, hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h1, hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h2272, h3443, h3889, hc12, hc24, hlam, hphi, p3891_1]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h2272, hlam, p3891_1]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h3327, hlam, p3891_1]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h2, hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h0, h3443, h3889, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3891_1]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h0, h3443, h3889, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3891_1]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h3443, hlam, p3891_1]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h3, hlam, p3891_0]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h0, h3443, h3889, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3891_1]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h0, h10, h3443, h3889, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3891_1]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [h0, h3443, h3889, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3891_1]
              · have p3891_0 := h3891c.1
                have p3891_1 := h3891c.2.1
                have p3891_2 := h3891c.2.2.1
                have p3891_3 := h3891c.2.2.2
                linarith only [hlam, p3891_0]
            · linarith only [h3787, h3889, h3890, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3973 | h3973
            · linarith only [h0, h1951, h3889, h3973, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h10, h3787, h3973, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1951 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2201 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 1 3 4 (by decide) (by decide) with h2272 | h2272
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1951 h2201 h2272
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1951 h2201 h2272

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1951 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h2201 | h2201
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1951 h2201
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1951 h2201

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h1951 | h1951
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1951
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1951

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10

set_option maxHeartbeats 11192000 in
set_option maxHeartbeats 11192000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s8_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  exact r1l7_11_13_25_L_I_L_I_H_I_s9 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

end R2N4
