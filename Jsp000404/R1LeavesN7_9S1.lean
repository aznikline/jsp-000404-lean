import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7_x0_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 5 (by decide) (by decide) with h339 | h339
  · rcases m.htr 1 4 5 (by decide) (by decide) with h340 | h340
    · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
      · linarith only [h0, h11, h339, h341, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
        · rcases m.htr 2 4 5 (by decide) (by decide) with h344 | h344
          · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
            · rcases h3bigk with h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                rcases p346_3 (m.d 0 3) (by simp) with h348 | h348
                · rcases p346_3 (m.d 1 3) (by simp) with h349 | h349
                  · linarith only [h1, h349, hlam]
                  · rcases p346_3 (m.d 2 3) (by simp) with h351 | h351
                    · linarith only [h351, h4, hlam]
                    · rcases p346_3 (m.d 3 4) (by simp) with h353 | h353
                      · linarith only [h353, h6, hlam]
                      · linarith only [h11, h353, hlam]
                · linarith only [h1, h348, hlam]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                rcases p346_3 (m.d 0 3) (by simp) with h357 | h357
                · rcases p346_3 (m.d 1 3) (by simp) with h358 | h358
                  · linarith only [h1, h358, hlam]
                  · linarith only [h358, h9, hlam]
                · linarith only [h357, h4, hlam]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h0, h11, h343, h345, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h11, h343, h6, h9, hlam, p346_2]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h1, hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h11, h343, h345, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p346_1]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h11, hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h0, h11, h345, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h4, hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h9, hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h341, hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h0, h345, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h6, hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h0, h339, h345, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h0, h343, h345, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                rcases p346_3 (m.d 0 3) (by simp) with h378 | h378
                · rcases p346_3 (m.d 1 3) (by simp) with h379 | h379
                  · linarith only [h11, h379, hlam]
                  · linarith only [h339, h379, hlam]
                · linarith only [h378, h7, hlam]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h7, hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h339, hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h343, hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [h345, hlam, p346_0]
              · have p346_0 := h346c.1
                have p346_1 := h346c.2.1
                have p346_2 := h346c.2.2.1
                have p346_3 := h346c.2.2.2
                linarith only [hlam, p346_0]
            · linarith only [h0, h11, h343, h345, h4, h6, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h11, h339, h340, h341, h343, h344, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h11, h339, h343, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h11, h339, h340, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
    · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
      · linarith only [h11, h393, h9, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h395 | h395
        · linarith only [h339, h395, h9, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h397 | h397
          · rcases m.htr 3 4 5 (by decide) (by decide) with h398 | h398
            · rcases h3bigk with h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h401 | h401
                · rcases p399_3 (m.d 1 3) (by simp) with h402 | h402
                  · linarith only [h1, h402, hlam]
                  · rcases p399_3 (m.d 2 3) (by simp) with h404 | h404
                    · linarith only [h4, h404, hlam]
                    · rcases p399_3 (m.d 3 4) (by simp) with h406 | h406
                      · linarith only [h406, h6, hlam]
                      · linarith only [h11, h406, hlam]
                · linarith only [h1, h401, hlam]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h410 | h410
                · rcases p399_3 (m.d 1 3) (by simp) with h411 | h411
                  · linarith only [h1, h411, hlam]
                  · linarith only [h411, h9, hlam]
                · linarith only [h4, h410, hlam]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h415 | h415
                · rcases p399_3 (m.d 1 3) (by simp) with h416 | h416
                  · linarith only [h1, h416, hlam]
                  · rcases p399_3 (m.d 2 3) (by simp) with h418 | h418
                    · linarith only [h4, h418, hlam]
                    · rcases p399_3 (m.d 3 4) (by simp) with h420 | h420
                      · linarith only [h420, hlam, p399_0]
                      · rcases p399_3 (m.d 3 5) (by simp) with h422 | h422
                        · linarith only [h422, h7, hlam]
                        · rcases h4bigk with h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [hlam, p424_0]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h0, h10, h397, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h0, h397, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h0, h339, h398, h4, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            rcases p424_3 (m.d 0 4) (by simp) with h429 | h429
                            · rcases p424_3 (m.d 1 4) (by simp) with h430 | h430
                              · linarith only [h2, h430, hlam]
                              · linarith only [h392, h430, hlam]
                            · linarith only [h429, hlam, p424_0]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h2, hlam, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [hlam, p424_0]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h397, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h11, hlam, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h0, h11, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p399_1, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h5, hlam, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h10, hlam, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [hlam, p424_0]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h393, hlam, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h6, hlam, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h0, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p399_1, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h0, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p399_1, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [hlam, p424_0]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p399_1, p424_1]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h8, hlam, p424_0]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h392, hlam, p424_0]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h397, hlam, p424_0]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [h398, hlam, p424_0]
                          · have p424_0 := h424c.1
                            have p424_1 := h424c.2.1
                            have p424_2 := h424c.2.2.1
                            have p424_3 := h424c.2.2.2
                            linarith only [hlam, p424_0]
                · linarith only [h415, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h455 | h455
                · rcases p399_3 (m.d 1 3) (by simp) with h456 | h456
                  · linarith only [h1, h456, hlam]
                  · rcases p399_3 (m.d 2 3) (by simp) with h458 | h458
                    · linarith only [h4, h458, hlam]
                    · rcases p399_3 (m.d 3 4) (by simp) with h460 | h460
                      · linarith only [h460, h6, hlam]
                      · linarith only [h398, h460, hlam]
                · linarith only [h455, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h1, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h339, hc23, hc35, hlam, hphi, p399_1]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h11, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h339, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h4, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h9, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h393, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h395, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h6, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h475 | h475
                · rcases p399_3 (m.d 1 3) (by simp) with h476 | h476
                  · linarith only [h476, hlam, p399_0]
                  · rcases p399_3 (m.d 2 3) (by simp) with h478 | h478
                    · linarith only [h393, h478, hlam]
                    · rcases p399_3 (m.d 3 4) (by simp) with h480 | h480
                      · rcases p399_3 (m.d 3 5) (by simp) with h481 | h481
                        · linarith only [h398, h481, hlam]
                        · linarith only [h339, h481, hlam]
                      · linarith only [h480, hlam, p399_0]
                · linarith only [h1, h475, hlam]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h486 | h486
                · rcases p399_3 (m.d 1 3) (by simp) with h487 | h487
                  · linarith only [h11, h487, hlam]
                  · linarith only [h487, h9, hlam]
                · linarith only [h4, h486, hlam]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h0, h339, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p399_1]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h7, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h494 | h494
                · rcases p399_3 (m.d 1 3) (by simp) with h495 | h495
                  · linarith only [h495, hlam, p399_0]
                  · rcases p399_3 (m.d 2 3) (by simp) with h497 | h497
                    · linarith only [h395, h497, hlam]
                    · rcases p399_3 (m.d 3 4) (by simp) with h499 | h499
                      · rcases p399_3 (m.d 3 5) (by simp) with h500 | h500
                        · rcases h4bigk with h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [hlam, p501_0]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h0, h10, h397, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h0, h397, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h0, h11, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            rcases p501_3 (m.d 0 4) (by simp) with h506 | h506
                            · rcases p501_3 (m.d 1 4) (by simp) with h507 | h507
                              · linarith only [h2, h507, hlam]
                              · linarith only [h392, h507, hlam]
                            · linarith only [h506, hlam, p501_0]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h2, hlam, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [hlam, p501_0]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h397, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h11, hlam, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h0, h11, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h5, hlam, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h10, hlam, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [hlam, p501_0]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h393, hlam, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h6, hlam, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [hlam, p501_0]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p501_1]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h8, hlam, p501_0]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h392, hlam, p501_0]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h397, hlam, p501_0]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [h398, hlam, p501_0]
                          · have p501_0 := h501c.1
                            have p501_1 := h501c.2.1
                            have p501_2 := h501c.2.2.1
                            have p501_3 := h501c.2.2.2
                            linarith only [hlam, p501_0]
                        · linarith only [h500, hlam, p399_0]
                      · linarith only [h11, h499, hlam]
                · linarith only [h1, h494, hlam]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h534 | h534
                · rcases p399_3 (m.d 1 3) (by simp) with h535 | h535
                  · linarith only [h339, h535, hlam]
                  · linarith only [h535, h9, hlam]
                · linarith only [h4, h534, hlam]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h398, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hlam, p399_0]
            · linarith only [h0, h10, h397, h398, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h542 | h542
            · rcases h3bigk with h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                rcases p543_3 (m.d 0 3) (by simp) with h545 | h545
                · rcases p543_3 (m.d 1 3) (by simp) with h546 | h546
                  · linarith only [h1, h546, hlam]
                  · rcases p543_3 (m.d 2 3) (by simp) with h548 | h548
                    · linarith only [h4, h548, hlam]
                    · rcases p543_3 (m.d 3 4) (by simp) with h550 | h550
                      · linarith only [h550, h6, hlam]
                      · linarith only [h11, h550, hlam]
                · linarith only [h1, h545, hlam]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h11, h392, h393, h397, h6, hlam, p543_2]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h0, h11, h392, h397, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p543_1]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                rcases p543_3 (m.d 0 3) (by simp) with h556 | h556
                · rcases p543_3 (m.d 1 3) (by simp) with h557 | h557
                  · linarith only [h1, h557, hlam]
                  · rcases p543_3 (m.d 2 3) (by simp) with h559 | h559
                    · linarith only [h4, h559, hlam]
                    · rcases p543_3 (m.d 3 4) (by simp) with h561 | h561
                      · linarith only [h561, h6, hlam]
                      · linarith only [h542, h561, hlam]
                · linarith only [h556, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h1, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h339, hc23, hc35, hlam, hphi, p543_1]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h11, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h339, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h4, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h9, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h393, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h395, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h6, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                rcases p543_3 (m.d 0 3) (by simp) with h576 | h576
                · rcases p543_3 (m.d 1 3) (by simp) with h577 | h577
                  · linarith only [h577, hlam, p543_0]
                  · rcases p543_3 (m.d 2 3) (by simp) with h579 | h579
                    · linarith only [h393, h579, hlam]
                    · rcases p543_3 (m.d 3 4) (by simp) with h581 | h581
                      · rcases p543_3 (m.d 3 5) (by simp) with h582 | h582
                        · linarith only [h542, h582, hlam]
                        · linarith only [h339, h582, hlam]
                      · linarith only [h581, hlam, p543_0]
                · linarith only [h1, h576, hlam]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                rcases p543_3 (m.d 0 3) (by simp) with h587 | h587
                · rcases p543_3 (m.d 1 3) (by simp) with h588 | h588
                  · linarith only [h11, h588, hlam]
                  · linarith only [h588, h9, hlam]
                · linarith only [h4, h587, hlam]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h339, hc13, hc34, hlam, hphi, p543_1]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h7, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                rcases p543_3 (m.d 0 3) (by simp) with h595 | h595
                · rcases p543_3 (m.d 1 3) (by simp) with h596 | h596
                  · linarith only [h596, hlam, p543_0]
                  · rcases p543_3 (m.d 2 3) (by simp) with h598 | h598
                    · linarith only [h395, h598, hlam]
                    · rcases p543_3 (m.d 3 4) (by simp) with h600 | h600
                      · rcases p543_3 (m.d 3 5) (by simp) with h601 | h601
                        · rcases h4bigk with h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [hlam, p602_0]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h0, h392, h393, h397, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            rcases p602_3 (m.d 0 4) (by simp) with h605 | h605
                            · rcases p602_3 (m.d 1 4) (by simp) with h606 | h606
                              · linarith only [h2, h606, hlam]
                              · linarith only [h10, h606, hlam]
                            · linarith only [h5, h605, hlam]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h0, h11, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h0, h393, h397, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h2, hlam, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [hlam, p602_0]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h2, h393, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h11, hlam, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h0, h11, h393, h397, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h5, hlam, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h10, hlam, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [hlam, p602_0]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h393, hlam, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h397, hlam, p602_0]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h6, hlam, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h0, h393, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [hlam, p602_0]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h0, h393, h397, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h8, hlam, p602_0]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h392, hlam, p602_0]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h392, h393, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p602_1]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [h542, hlam, p602_0]
                          · have p602_0 := h602c.1
                            have p602_1 := h602c.2.1
                            have p602_2 := h602c.2.2.1
                            have p602_3 := h602c.2.2.2
                            linarith only [hlam, p602_0]
                        · linarith only [h601, hlam, p543_0]
                      · linarith only [h11, h600, hlam]
                · linarith only [h1, h595, hlam]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                rcases p543_3 (m.d 0 3) (by simp) with h635 | h635
                · rcases p543_3 (m.d 1 3) (by simp) with h636 | h636
                  · linarith only [h339, h636, hlam]
                  · linarith only [h636, h9, hlam]
                · linarith only [h4, h635, hlam]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [h542, hlam, p543_0]
              · have p543_0 := h543c.1
                have p543_1 := h543c.2.1
                have p543_2 := h543c.2.2.1
                have p543_3 := h543c.2.2.2
                linarith only [hlam, p543_0]
            · linarith only [h11, h392, h542, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
      · linarith only [h11, h643, h9, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h645 | h645
        · linarith only [h339, h645, h9, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h647 | h647
          · linarith only [h0, h10, h392, h647, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h649 | h649
            · rcases h3bigk with h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h11, h392, h6, h649, hlam, p650_2]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h11, h392, h6, h649, h9, hlam, p650_2]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h0, h11, h392, h4, h649, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                rcases p650_3 (m.d 0 3) (by simp) with h655 | h655
                · rcases p650_3 (m.d 1 3) (by simp) with h656 | h656
                  · linarith only [h1, h656, hlam]
                  · rcases p650_3 (m.d 2 3) (by simp) with h658 | h658
                    · linarith only [h4, h658, hlam]
                    · rcases p650_3 (m.d 3 4) (by simp) with h660 | h660
                      · linarith only [h6, h660, hlam]
                      · linarith only [h649, h660, hlam]
                · linarith only [h655, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h1, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h11, h392, h649, hc23, hc34, hlam, hphi, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h11, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h339, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h4, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h9, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h643, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h645, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h6, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                rcases p650_3 (m.d 0 3) (by simp) with h675 | h675
                · rcases p650_3 (m.d 1 3) (by simp) with h676 | h676
                  · linarith only [h676, hlam, p650_0]
                  · rcases p650_3 (m.d 2 3) (by simp) with h678 | h678
                    · linarith only [h643, h678, hlam]
                    · rcases p650_3 (m.d 3 4) (by simp) with h680 | h680
                      · rcases p650_3 (m.d 3 5) (by simp) with h681 | h681
                        · linarith only [h649, h681, hlam]
                        · linarith only [h339, h681, hlam]
                      · linarith only [h680, hlam, p650_0]
                · linarith only [h1, h675, hlam]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                rcases p650_3 (m.d 0 3) (by simp) with h686 | h686
                · rcases p650_3 (m.d 1 3) (by simp) with h687 | h687
                  · linarith only [h11, h687, hlam]
                  · linarith only [h687, h9, hlam]
                · linarith only [h4, h686, hlam]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h0, h11, h392, h4, h6, h649, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h7, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                rcases p650_3 (m.d 0 3) (by simp) with h694 | h694
                · rcases p650_3 (m.d 1 3) (by simp) with h695 | h695
                  · linarith only [h695, hlam, p650_0]
                  · rcases p650_3 (m.d 2 3) (by simp) with h697 | h697
                    · linarith only [h645, h697, hlam]
                    · rcases p650_3 (m.d 3 4) (by simp) with h699 | h699
                      · rcases p650_3 (m.d 3 5) (by simp) with h700 | h700
                        · rcases h4bigk with h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            rcases p701_3 (m.d 0 4) (by simp) with h703 | h703
                            · rcases p701_3 (m.d 1 4) (by simp) with h704 | h704
                              · linarith only [h2, h704, hlam]
                              · rcases p701_3 (m.d 2 4) (by simp) with h706 | h706
                                · linarith only [h5, h706, hlam]
                                · rcases p701_3 (m.d 3 4) (by simp) with h708 | h708
                                  · linarith only [h6, h708, hlam]
                                  · linarith only [h11, h708, hlam]
                            · linarith only [h2, h703, hlam]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            rcases p701_3 (m.d 0 4) (by simp) with h712 | h712
                            · rcases p701_3 (m.d 1 4) (by simp) with h713 | h713
                              · linarith only [h2, h713, hlam]
                              · linarith only [h10, h713, hlam]
                            · linarith only [h5, h712, hlam]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h0, h11, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h0, h11, h392, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h2, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h392, h643, hc23, hc45, hlam, hphi, ht34, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h11, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h392, hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h5, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h10, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h643, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h647, hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h6, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h0, h4, h6, h643, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h8, hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h10, h643, hc23, hc45, hlam, hphi, ht34, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h0, h4, h6, h643, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h649, hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [hlam, p701_0]
                        · linarith only [h700, hlam, p650_0]
                      · linarith only [h11, h699, hlam]
                · linarith only [h1, h694, hlam]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                rcases p650_3 (m.d 0 3) (by simp) with h742 | h742
                · rcases p650_3 (m.d 1 3) (by simp) with h743 | h743
                  · linarith only [h339, h743, hlam]
                  · linarith only [h743, h9, hlam]
                · linarith only [h4, h742, hlam]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h649, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hlam, p650_0]
            · rcases h3bigk with h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h11, h6, h649, h8, hlam, p749_2]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h11, h6, h649, h8, h9, hlam, p749_2]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                rcases p749_3 (m.d 0 3) (by simp) with h753 | h753
                · rcases p749_3 (m.d 1 3) (by simp) with h754 | h754
                  · linarith only [h1, h754, hlam]
                  · rcases p749_3 (m.d 2 3) (by simp) with h756 | h756
                    · linarith only [h4, h756, hlam]
                    · rcases p749_3 (m.d 3 4) (by simp) with h758 | h758
                      · linarith only [h758, hlam, p749_0]
                      · rcases p749_3 (m.d 3 5) (by simp) with h760 | h760
                        · linarith only [h7, h760, hlam]
                        · linarith only [h649, h760, hlam]
                · linarith only [h753, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                rcases p749_3 (m.d 0 3) (by simp) with h764 | h764
                · rcases p749_3 (m.d 1 3) (by simp) with h765 | h765
                  · linarith only [h1, h765, hlam]
                  · rcases p749_3 (m.d 2 3) (by simp) with h767 | h767
                    · linarith only [h4, h767, hlam]
                    · rcases p749_3 (m.d 3 4) (by simp) with h769 | h769
                      · linarith only [h6, h769, hlam]
                      · rcases p749_3 (m.d 3 5) (by simp) with h771 | h771
                        · linarith only [h771, hlam, p749_0]
                        · rcases h4bigk with h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [hlam, p773_0]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            rcases p773_3 (m.d 0 4) (by simp) with h775 | h775
                            · rcases p773_3 (m.d 1 4) (by simp) with h776 | h776
                              · linarith only [h2, h776, hlam]
                              · rcases p773_3 (m.d 2 4) (by simp) with h778 | h778
                                · linarith only [h5, h778, hlam]
                                · rcases p773_3 (m.d 3 4) (by simp) with h780 | h780
                                  · linarith only [h6, h780, hlam]
                                  · linarith only [h11, h780, hlam]
                            · linarith only [h2, h775, hlam]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            rcases p773_3 (m.d 0 4) (by simp) with h784 | h784
                            · rcases p773_3 (m.d 1 4) (by simp) with h785 | h785
                              · linarith only [h2, h785, hlam]
                              · linarith only [h10, h785, hlam]
                            · linarith only [h5, h784, hlam]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h11, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h0, h11, h4, h6, h649, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h2, hlam, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [hlam, p773_0]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h2, h643, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h11, hlam, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h392, hlam, p773_0]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h5, hlam, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h10, hlam, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [hlam, p773_0]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h643, hlam, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h647, hlam, p773_0]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h6, hlam, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h649, hc14, hc45, hlam, hphi, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h0, h4, h6, h643, h649, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [hlam, p773_0]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h649, hlam, p773_0]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h8, hlam, p773_0]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h0, h10, h4, h6, h643, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h0, h4, h6, h643, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [h0, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p773_1]
                          · have p773_0 := h773c.1
                            have p773_1 := h773c.2.1
                            have p773_2 := h773c.2.2.1
                            have p773_3 := h773c.2.2.2
                            linarith only [hlam, p773_0]
                · linarith only [h764, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h1, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h11, hc23, hc34, hlam, hphi, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h11, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h339, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h4, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h9, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h643, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h645, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h6, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h0, h4, h6, h649, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h0, h4, h6, h649, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h649, hlam, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h7, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                rcases p749_3 (m.d 0 3) (by simp) with h828 | h828
                · rcases p749_3 (m.d 1 3) (by simp) with h829 | h829
                  · linarith only [h829, hlam, p749_0]
                  · rcases p749_3 (m.d 2 3) (by simp) with h831 | h831
                    · linarith only [h645, h831, hlam]
                    · rcases p749_3 (m.d 3 4) (by simp) with h833 | h833
                      · linarith only [h649, h833, hlam]
                      · linarith only [h11, h833, hlam]
                · linarith only [h1, h828, hlam]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                rcases p749_3 (m.d 0 3) (by simp) with h837 | h837
                · rcases p749_3 (m.d 1 3) (by simp) with h838 | h838
                  · linarith only [h339, h838, hlam]
                  · linarith only [h838, h9, hlam]
                · linarith only [h4, h837, hlam]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h11, h9, hc23, hc35, hlam, hphi, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hlam, p749_0]

set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
  · exact r1l7_13_24_L_I_H_I_s7_x0_x0_x0_x0 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h10 h11
  · exact r1l7_13_24_L_I_H_I_s7_x0_x0_x0_x1 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h10 h11

set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 4 (by decide) (by decide) with h844 | h844
  · linarith only [h10, h844, h9, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h846 | h846
    · rcases m.htr 1 4 5 (by decide) (by decide) with h847 | h847
      · rcases m.htr 2 3 4 (by decide) (by decide) with h848 | h848
        · linarith only [h0, h4, h844, h846, h848, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h850 | h850
          · linarith only [h0, h10, h4, h6, h848, h850, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10, h4, h6, h846, h848, h850, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · linarith only [h10, h846, h847, h9, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h854 | h854
      · rcases m.htr 2 3 4 (by decide) (by decide) with h855 | h855
        · linarith only [h0, h10, h5, h855, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h857 | h857
          · linarith only [h0, h10, h4, h6, h846, h855, h857, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h859 | h859
            · rcases m.htr 3 4 5 (by decide) (by decide) with h860 | h860
              · rcases h3bigk with h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  rcases p861_3 (m.d 0 3) (by simp) with h863 | h863
                  · rcases p861_3 (m.d 1 3) (by simp) with h864 | h864
                    · linarith only [h1, h864, hlam]
                    · rcases p861_3 (m.d 2 3) (by simp) with h866 | h866
                      · linarith only [h4, h866, hlam]
                      · rcases p861_3 (m.d 3 4) (by simp) with h868 | h868
                        · linarith only [h6, h868, hlam]
                        · linarith only [h844, h868, hlam]
                  · linarith only [h1, h863, hlam]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h10, h6, h855, h9, hlam, p861_2]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h0, h10, h4, h855, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p861_1]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  rcases p861_3 (m.d 0 3) (by simp) with h874 | h874
                  · rcases p861_3 (m.d 1 3) (by simp) with h875 | h875
                    · linarith only [h1, h875, hlam]
                    · rcases p861_3 (m.d 2 3) (by simp) with h877 | h877
                      · linarith only [h4, h877, hlam]
                      · rcases p861_3 (m.d 3 4) (by simp) with h879 | h879
                        · linarith only [h6, h879, hlam]
                        · linarith only [h860, h879, hlam]
                  · linarith only [h874, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h1, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h846, hc23, hc35, hlam, hphi, p861_1]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h844, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h846, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h4, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h9, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h855, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h857, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h6, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  rcases p861_3 (m.d 0 3) (by simp) with h894 | h894
                  · rcases p861_3 (m.d 1 3) (by simp) with h895 | h895
                    · linarith only [h895, hlam, p861_0]
                    · rcases p861_3 (m.d 2 3) (by simp) with h897 | h897
                      · linarith only [h855, h897, hlam]
                      · rcases p861_3 (m.d 3 4) (by simp) with h899 | h899
                        · rcases p861_3 (m.d 3 5) (by simp) with h900 | h900
                          · linarith only [h860, h900, hlam]
                          · linarith only [h846, h900, hlam]
                        · linarith only [h899, hlam, p861_0]
                  · linarith only [h1, h894, hlam]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  rcases p861_3 (m.d 0 3) (by simp) with h905 | h905
                  · rcases p861_3 (m.d 1 3) (by simp) with h906 | h906
                    · linarith only [h844, h906, hlam]
                    · linarith only [h9, h906, hlam]
                  · linarith only [h4, h905, hlam]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h0, h4, h6, h846, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p861_1]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h7, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  rcases p861_3 (m.d 0 3) (by simp) with h913 | h913
                  · rcases p861_3 (m.d 1 3) (by simp) with h914 | h914
                    · linarith only [h914, hlam, p861_0]
                    · rcases p861_3 (m.d 2 3) (by simp) with h916 | h916
                      · linarith only [h857, h916, hlam]
                      · rcases p861_3 (m.d 3 4) (by simp) with h918 | h918
                        · rcases p861_3 (m.d 3 5) (by simp) with h919 | h919
                          · rcases h4bigk with h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [hlam, p920_0]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h0, h4, h6, h854, hc01, hc45, hlam, hphi, ht0b, ht5b, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h0, h10, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h0, h4, h6, h844, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              rcases p920_3 (m.d 0 4) (by simp) with h925 | h925
                              · rcases p920_3 (m.d 1 4) (by simp) with h926 | h926
                                · linarith only [h2, h926, hlam]
                                · linarith only [h854, h926, hlam]
                              · linarith only [h925, hlam, p920_0]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h2, hlam, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [hlam, p920_0]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h10, hlam, p920_0]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h844, hlam, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h5, hlam, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [hlam, p920_0]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h855, hlam, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h6, hlam, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h0, h10, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [hlam, p920_0]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h0, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p920_1]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h8, hlam, p920_0]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h854, hlam, p920_0]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h859, hlam, p920_0]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [h860, hlam, p920_0]
                            · have p920_0 := h920c.1
                              have p920_1 := h920c.2.1
                              have p920_2 := h920c.2.2.1
                              have p920_3 := h920c.2.2.2
                              linarith only [hlam, p920_0]
                          · linarith only [h919, hlam, p861_0]
                        · linarith only [h844, h918, hlam]
                  · linarith only [h1, h913, hlam]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  rcases p861_3 (m.d 0 3) (by simp) with h953 | h953
                  · rcases p861_3 (m.d 1 3) (by simp) with h954 | h954
                    · linarith only [h846, h954, hlam]
                    · linarith only [h9, h954, hlam]
                  · linarith only [h4, h953, hlam]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [h860, hlam, p861_0]
                · have p861_0 := h861c.1
                  have p861_1 := h861c.2.1
                  have p861_2 := h861c.2.2.1
                  have p861_3 := h861c.2.2.2
                  linarith only [hlam, p861_0]
              · linarith only [h844, h854, h860, hlam]
            · linarith only [h10, h854, h859, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h962 | h962
        · linarith only [h0, h10, h5, h9, h962, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h964 | h964
          · linarith only [h0, h10, h4, h6, h8, h854, h9, h964, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h966 | h966
            · linarith only [h10, h854, h9, h962, h966, hc23, hc34, hlam, hphi]
            · linarith only [h0, h10, h4, h6, h8, h9, h966, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
  · exact r1l7_13_24_L_I_H_I_s7_x0_x0_x0 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h10
  · exact r1l7_13_24_L_I_H_I_s7_x0_x0_x1 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h10

end R2N4
