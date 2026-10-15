import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_75S9

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_H_I_L_0_L_R_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h388 | h388
  · rcases m.htr 0 2 4 (by decide) (by decide) with h389 | h389
    · rcases m.htr 0 2 5 (by decide) (by decide) with h390 | h390
      · rcases m.htr 0 3 4 (by decide) (by decide) with h391 | h391
        · rcases m.htr 1 2 3 (by decide) (by decide) with h392 | h392
          · rcases m.htr 1 2 4 (by decide) (by decide) with h393 | h393
            · rcases m.htr 1 2 5 (by decide) (by decide) with h394 | h394
              · rcases m.htr 2 3 4 (by decide) (by decide) with h395 | h395
                · rcases m.htr 2 3 5 (by decide) (by decide) with h396 | h396
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h397 | h397
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h398 | h398
                      · linarith only [h391, h398, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                      · rcases h2bigk with h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h0, hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h395, h397, h398, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p400_1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h0, h397, h398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p400_1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h0, h397, h398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p400_1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p400_1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h395, h397, h398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p400_1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h397, h398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p400_1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h397, h398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p400_1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h388, hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h392, hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h388, h397, h398, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p400_1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h392, h397, h398, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p400_1, u3elo1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h389, hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h393, hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h395, hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h389, h397, h398, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p400_1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h390, hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h394, hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h396, hlam, p400_0]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [h397, hlam, p400_1]
                        · have p400_0 := h400c.1
                          have p400_1 := h400c.2.1
                          have p400_2 := h400c.2.2.1
                          have p400_3 := h400c.2.2.2
                          linarith only [hlam, p400_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h426 | h426
                      · linarith only [h391, h397, h426, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · rcases h2bigk with h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h0, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h0, h396, hc12, hlam, hphi, ht01, ht0b, ht5b, p428_1, u5ehi2]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          rcases p428_3 (m.d 0 2) (by simp) with h432 | h432
                          · rcases p428_3 (m.d 1 2) (by simp) with h433 | h433
                            · rcases p428_3 (m.d 2 3) (by simp) with h434 | h434
                              · linarith only [h388, h434, hlam]
                              · linarith only [h395, h434, hlam]
                            · linarith only [h393, h433, hlam]
                          · linarith only [h432, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h0, h396, hc12, hlam, hphi, ht01, ht0b, ht5b, p428_1, u5ehi3]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h396, hc12, hlam, hphi, ht01, ht0b, ht5b, p428_1, u5ehi3]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          rcases p428_3 (m.d 0 2) (by simp) with h443 | h443
                          · linarith only [h0, h443, hlam]
                          · linarith only [h389, h443, hlam]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h396, hc12, hlam, hphi, ht01, ht0b, ht5b, p428_1, u5ehi3]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h388, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h392, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h388, h395, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h388, h396, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p428_1, u3elo0, u5ehi3]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h389, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h393, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h395, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h397, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h390, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h394, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h396, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h395, h397, hc34, hc45, hlam, hphi, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h462 | h462
                    · linarith only [h395, h396, h462, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h464 | h464
                      · linarith only [h391, h462, h464, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi2]
                      · rcases h2bigk with h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h0, hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h0, h395, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p466_1]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          rcases p466_3 (m.d 0 2) (by simp) with h470 | h470
                          · rcases p466_3 (m.d 1 2) (by simp) with h471 | h471
                            · rcases p466_3 (m.d 2 3) (by simp) with h472 | h472
                              · linarith only [h388, h472, hlam]
                              · linarith only [h395, h472, hlam]
                            · linarith only [h393, h471, hlam]
                          · linarith only [h470, hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h0, h395, h396, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p466_1]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p466_1]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h395, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p466_1]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          rcases p466_3 (m.d 0 2) (by simp) with h481 | h481
                          · linarith only [h0, h481, hlam]
                          · linarith only [h389, h481, hlam]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h395, h396, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p466_1]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h388, hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h392, hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h395, h396, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p466_1, u3elo4]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h396, hlam, p466_1]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h389, hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h393, hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h395, hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h462, hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h390, hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h394, hlam, p466_0]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h390, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p466_1]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [h395, h396, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p466_1, u3elo4]
                        · have p466_0 := h466c.1
                          have p466_1 := h466c.2.1
                          have p466_2 := h466c.2.2.1
                          have p466_3 := h466c.2.2.2
                          linarith only [hlam, p466_0]
                · linarith only [h391, h395, hc23, hlam, hphi, u3elo0]
              · linarith only [h0, h390, h394, hlam]
            · linarith only [h0, h389, h393, hlam]
          · linarith only [h0, h390, h392, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
          · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
            · rcases m.htr 1 2 5 (by decide) (by decide) with h506 | h506
              · rcases m.htr 2 3 4 (by decide) (by decide) with h507 | h507
                · linarith only [h391, h507, hc03, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h509 | h509
                  · linarith only [h388, h391, h509, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h511 | h511
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h512 | h512
                      · rcases h2bigk with h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h0, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          rcases p513_3 (m.d 0 2) (by simp) with h516 | h516
                          · rcases p513_3 (m.d 1 2) (by simp) with h517 | h517
                            · rcases p513_3 (m.d 2 3) (by simp) with h518 | h518
                              · linarith only [h518, hlam, p513_0]
                              · rcases p513_3 (m.d 2 4) (by simp) with h520 | h520
                                · linarith only [h389, h520, hlam]
                                · linarith only [h507, h520, hlam]
                            · linarith only [h504, h517, hlam]
                          · linarith only [h516, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h0, h511, hc12, hlam, hphi, ht01, ht0b, ht5b, p513_1, u5ehi4]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p513_1, u5ehi2]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h390, hc12, hlam, hphi, ht01, ht0b, ht5b, p513_1, u5ehi0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          rcases p513_3 (m.d 0 2) (by simp) with h529 | h529
                          · linarith only [h0, h529, hlam]
                          · linarith only [h388, h529, hlam]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h511, hc12, hlam, hphi, ht01, ht0b, ht5b, p513_1, u5ehi4]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h511, hc12, hlam, hphi, ht01, ht0b, ht5b, p513_1, u5ehi4]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h388, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h504, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h507, hlam, p513_1]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h509, hlam, p513_1]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h389, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h505, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h389, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p513_1]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h389, h391, h511, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p513_1, u3elo3, u5ehi4]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h390, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h506, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h0, h390, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p513_1]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h511, hlam, p513_1]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [hlam, p513_0]
                      · linarith only [h389, h391, h511, h512, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h550 | h550
                      · linarith only [h507, h511, h550, hc23, hlam, hphi, u3elo3]
                      · rcases h2bigk with h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h0, hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          rcases p552_3 (m.d 0 2) (by simp) with h555 | h555
                          · rcases p552_3 (m.d 1 2) (by simp) with h556 | h556
                            · rcases p552_3 (m.d 2 3) (by simp) with h557 | h557
                              · linarith only [h557, hlam, p552_0]
                              · rcases p552_3 (m.d 2 4) (by simp) with h559 | h559
                                · linarith only [h389, h559, hlam]
                                · linarith only [h507, h559, hlam]
                            · linarith only [h504, h556, hlam]
                          · linarith only [h555, hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          rcases p552_3 (m.d 0 2) (by simp) with h564 | h564
                          · rcases p552_3 (m.d 1 2) (by simp) with h565 | h565
                            · rcases p552_3 (m.d 2 3) (by simp) with h566 | h566
                              · linarith only [h388, h566, hlam]
                              · rcases p552_3 (m.d 2 4) (by simp) with h568 | h568
                                · linarith only [h568, hlam, p552_0]
                                · rcases p552_3 (m.d 2 5) (by simp) with h570 | h570
                                  · linarith only [h390, h570, hlam]
                                  · linarith only [h511, h570, hlam]
                            · linarith only [h505, h565, hlam]
                          · linarith only [h564, hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p552_1, u5ehi2]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p552_1]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          rcases p552_3 (m.d 0 2) (by simp) with h578 | h578
                          · linarith only [h0, h578, hlam]
                          · linarith only [h388, h578, hlam]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          rcases p552_3 (m.d 0 2) (by simp) with h581 | h581
                          · linarith only [h0, h581, hlam]
                          · linarith only [h389, h581, hlam]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p552_1, u5ehi2]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h388, hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h504, hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h507, hlam, p552_1]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h509, hlam, p552_1]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h389, hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h505, hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h389, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p552_1]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h511, hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h390, hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h506, hlam, p552_0]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h0, h390, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p552_1]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [h509, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p552_1, u3elo4]
                        · have p552_0 := h552c.1
                          have p552_1 := h552c.2.1
                          have p552_2 := h552c.2.2.1
                          have p552_3 := h552c.2.2.2
                          linarith only [hlam, p552_0]
              · linarith only [h0, h390, h506, hlam]
            · linarith only [h0, h389, h505, hlam]
          · linarith only [h0, h388, h391, h504, hc02, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h603 | h603
        · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
          · rcases m.htr 1 2 4 (by decide) (by decide) with h605 | h605
            · rcases m.htr 1 2 5 (by decide) (by decide) with h606 | h606
              · rcases m.htr 2 3 4 (by decide) (by decide) with h607 | h607
                · linarith only [h388, h390, h606, h607, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h388, h390, h603, h606, h607, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h610 | h610
                · rcases m.htr 2 3 5 (by decide) (by decide) with h611 | h611
                  · linarith only [h0, h388, h606, h611, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h606, h611, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h603, h610, hc23, hlam, hphi, u3elo0]
            · linarith only [h0, h389, h605, hlam]
          · linarith only [h0, h604, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h617 | h617
          · rcases m.htr 1 2 4 (by decide) (by decide) with h618 | h618
            · rcases m.htr 1 2 5 (by decide) (by decide) with h619 | h619
              · rcases m.htr 2 3 4 (by decide) (by decide) with h620 | h620
                · linarith only [h388, h390, h603, h619, h620, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h622 | h622
                  · linarith only [h388, h603, h622, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · linarith only [h389, h390, h620, h622, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h625 | h625
                · linarith only [h603, h625, hc03, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h627 | h627
                  · linarith only [h388, h603, h627, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · linarith only [h0, h619, h627, hc01, hlam, hphi, ht12, ht23, u3elo4]
            · linarith only [h0, h389, h618, hlam]
          · linarith only [h0, h388, h603, h617, hc02, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h632 | h632
      · rcases m.htr 0 3 4 (by decide) (by decide) with h633 | h633
        · linarith only [h388, h389, h633, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
          · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
            · linarith only [h389, h632, h636, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h638 | h638
              · rcases m.htr 2 3 4 (by decide) (by decide) with h639 | h639
                · linarith only [h388, h389, h632, h633, h639, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi2]
                · linarith only [h0, h636, h639, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h632, h638, hlam]
          · linarith only [h0, h388, h635, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h644 | h644
        · linarith only [h388, h389, h644, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h646 | h646
          · rcases m.htr 1 2 4 (by decide) (by decide) with h647 | h647
            · rcases m.htr 1 2 5 (by decide) (by decide) with h648 | h648
              · rcases m.htr 2 3 4 (by decide) (by decide) with h649 | h649
                · linarith only [h388, h389, h644, h647, h649, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h388, h389, h649, hc23, hlam, hphi, u3elo3]
              · linarith only [h388, h389, h647, h648, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h653 | h653
              · linarith only [h388, h632, h647, h653, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h655 | h655
                · linarith only [h388, h644, h655, hlam]
                · linarith only [h0, h647, h655, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h388, h389, h646, hc01, hc24, hlam, hphi, ht12]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h659 | h659
    · rcases m.htr 0 2 5 (by decide) (by decide) with h660 | h660
      · linarith only [h388, h660, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h662 | h662
        · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
          · rcases m.htr 1 2 4 (by decide) (by decide) with h664 | h664
            · rcases m.htr 1 2 5 (by decide) (by decide) with h665 | h665
              · rcases m.htr 2 3 4 (by decide) (by decide) with h666 | h666
                · rcases m.htr 2 3 5 (by decide) (by decide) with h667 | h667
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h668 | h668
                    · linarith only [h659, h660, h663, h667, h668, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h670 | h670
                      · linarith only [h659, h660, h666, h668, h670, hlam]
                      · rcases h2bigk with h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h0, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h388, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h660, h663, h667, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p672_1, u3elo1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h660, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p672_1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h660, h667, hc12, hlam, hphi, ht01, ht0b, ht5b, p672_1, u5ehi0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          rcases p672_3 (m.d 0 2) (by simp) with h681 | h681
                          · linarith only [h0, h681, hlam]
                          · linarith only [h659, h681, hlam]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h659, h660, h666, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p672_1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h659, h663, h666, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p672_1, u3elo1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h663, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h663, h666, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p672_1, u3elo1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h659, h660, h663, h666, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p672_1, u3elo1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h659, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h664, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h666, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h668, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h659, h665, h666, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p672_1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h665, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h667, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h663, h666, h667, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p672_1, u3elo1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hlam, p672_0]
                  · linarith only [h388, h659, h666, h667, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h388, h659, h666, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h388, h659, h663, h665, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h388, h659, h663, h664, hlam]
          · linarith only [h0, h663, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h388, h659, h662, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h706 | h706
      · linarith only [h388, h706, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h708 | h708
        · rcases m.htr 1 2 3 (by decide) (by decide) with h709 | h709
          · rcases m.htr 1 2 4 (by decide) (by decide) with h710 | h710
            · rcases m.htr 1 2 5 (by decide) (by decide) with h711 | h711
              · rcases m.htr 2 3 4 (by decide) (by decide) with h712 | h712
                · rcases m.htr 2 3 5 (by decide) (by decide) with h713 | h713
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h714 | h714
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h715 | h715
                      · linarith only [h708, h715, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                      · rcases h2bigk with h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h0, hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h388, hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h659, hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h706, hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p717_1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h712, h714, h715, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p717_1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h714, h715, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p717_1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h0, h706, hc01, hc12, hlam, hphi, p717_1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h0, h709, hc01, hlam, hphi, ht12, ht23, p717_1, u3elo1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h709, hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h709, h714, h715, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p717_1, u3elo1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h0, h706, h709, hc01, hlam, hphi, ht12, ht23, p717_1, u3elo1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h0, h710, hc01, hc14, hlam, hphi, p717_1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h710, hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h712, hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h0, h706, h709, h712, hc01, hlam, hphi, ht12, ht23, p717_1, u3elo1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p717_1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h711, hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h713, hlam, p717_0]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [h714, hlam, p717_1]
                        · have p717_0 := h717c.1
                          have p717_1 := h717c.2.1
                          have p717_2 := h717c.2.2.1
                          have p717_3 := h717c.2.2.2
                          linarith only [hlam, p717_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h743 | h743
                      · linarith only [h0, h659, h714, h743, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases h2bigk with h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h0, hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h388, hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h659, hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h706, hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p745_1]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h713, hc12, hlam, hphi, ht01, ht0b, ht5b, p745_1, u5ehi2]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h0, h659, hc01, hc12, hlam, hphi, p745_1]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h0, h706, hc01, hc12, hlam, hphi, p745_1]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h0, h709, hc01, hc13, hlam, hphi, p745_1]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h709, hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h0, h659, h709, hc01, hlam, hphi, ht12, ht23, p745_1, u3elo1]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h0, h706, h709, hc01, hlam, hphi, ht12, ht23, p745_1, u3elo1]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p745_1]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h710, hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h712, hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h714, hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p745_1]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h711, hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h713, hlam, p745_0]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [h709, h713, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p745_1, u3elo1]
                        · have p745_0 := h745c.1
                          have p745_1 := h745c.2.1
                          have p745_2 := h745c.2.2.1
                          have p745_3 := h745c.2.2.2
                          linarith only [hlam, p745_0]
                  · linarith only [h0, h388, h713, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h0, h388, h712, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h388, h709, h711, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h388, h709, h710, hc01, hc24, hlam, hphi, ht12]
          · linarith only [h0, h709, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h776 | h776
          · rcases m.htr 1 2 4 (by decide) (by decide) with h777 | h777
            · rcases m.htr 1 2 5 (by decide) (by decide) with h778 | h778
              · rcases m.htr 2 3 4 (by decide) (by decide) with h779 | h779
                · linarith only [h708, h776, h779, hc03, hlam, hphi, u3elo1]
                · linarith only [h0, h388, h779, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h388, h776, h778, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h388, h776, h777, hc01, hc24, hlam, hphi, ht12]
          · linarith only [h0, h776, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_22_13_15_H_I_L_0_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_15_H_I_L_0_L_R_x0 m hb2 hb3 hb5 h0
  · exact r1l7_22_13_15_H_I_L_0_L_R_x1 m hb2 hb3 hb5 h0

end R2N4
