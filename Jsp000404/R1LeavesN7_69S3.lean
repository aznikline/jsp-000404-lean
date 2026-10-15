import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_69S2

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_25_L_0_L_R_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h456 | h456
  · rcases m.htr 0 2 4 (by decide) (by decide) with h457 | h457
    · rcases m.htr 0 2 5 (by decide) (by decide) with h458 | h458
      · rcases m.htr 0 3 5 (by decide) (by decide) with h459 | h459
        · rcases m.htr 0 4 5 (by decide) (by decide) with h460 | h460
          · rcases m.htr 1 2 3 (by decide) (by decide) with h461 | h461
            · rcases m.htr 1 2 5 (by decide) (by decide) with h462 | h462
              · rcases m.htr 1 3 4 (by decide) (by decide) with h463 | h463
                · rcases m.htr 1 3 5 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h467 | h467
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h468 | h468
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h469 | h469
                            · linarith only [h456, h466, h469, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h456, h466, h468, h469, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h460, h468, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                        · linarith only [h459, h467, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h474 | h474
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h475 | h475
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h476 | h476
                            · rcases h5bigk with h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h0, hlam, p477_1]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p477_1, u0elo4, u2ehi4]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h456, h459, hc35, hlam, hphi, ht0b, ht5b, p477_1, u0elo1]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h456, h459, hc45, hlam, hphi, ht0b, ht5b, p477_1, u0elo1]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p477_1]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h462, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p477_1, u2ehi4]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                rcases p477_3 (m.d 0 5) (by simp) with h486 | h486
                                · linarith only [h0, h486, hlam]
                                · linarith only [h459, h486, hlam]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                rcases p477_3 (m.d 0 5) (by simp) with h489 | h489
                                · linarith only [h0, h489, hlam]
                                · linarith only [h460, h489, hlam]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h458, hlam, p477_1]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h462, hlam, p477_1]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h458, h476, hc45, hlam, hphi, ht0b, ht5b, p477_1, u0elo4]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h461, h463, h466, h474, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p477_1]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h459, hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h464, hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h474, hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h456, h459, hc45, hlam, hphi, ht0b, ht5b, p477_1, u0elo1]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h460, hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h465, hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h475, hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [h476, hlam, p477_0]
                              · have p477_0 := h477c.1
                                have p477_1 := h477c.2.1
                                have p477_2 := h477c.2.2.1
                                have p477_3 := h477c.2.2.2
                                linarith only [hlam, p477_0]
                            · linarith only [h466, h474, h476, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                          · linarith only [h457, h460, h466, h474, h475, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi4]
                        · linarith only [h456, h459, h474, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h0, h460, h465, hlam]
                  · linarith only [h456, h459, h461, h464, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h513 | h513
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                      · linarith only [h461, h463, h512, h514, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h516 | h516
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h517 | h517
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h518 | h518
                            · rcases h5bigk with h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h0, hlam, p519_1]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p519_1, u0elo4, u2ehi4]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [hc35, hlam, hphi, ht0b, ht5b, p519_1, u0elo4]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h0, h457, h463, h512, h514, h516, hc34, hc45, hlam, hphi, ht0b, ht23, ht5b, p519_1, u0elo1, u2ehi4]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h457, h463, h512, h514, h516, hc05, hc34, hlam, hphi, ht0b, ht23, ht5b, p519_1, u0elo1, u2ehi4]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h463, h512, hc34, hlam, hphi, ht23, p519_1, u2ehi4]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h457, h463, h512, h514, h516, h518, hc34, hc45, hlam, hphi, ht0b, ht23, ht5b, p519_1, u0elo1, u2ehi4]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h457, h463, h512, h514, h516, hc34, hc45, hlam, hphi, ht0b, ht23, ht5b, p519_1, u0elo1, u2ehi4]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h458, hlam, p519_1]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h462, hlam, p519_1]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h457, h514, h516, h518, hc45, hlam, hphi, ht0b, ht5b, p519_1, u0elo1]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h457, h514, h516, hc45, hlam, hphi, ht0b, ht5b, p519_1, u0elo1]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h459, hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h512, hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h516, hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h456, h459, hc45, hlam, hphi, ht0b, ht5b, p519_1, u0elo1]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h460, hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h513, hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h517, hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [h518, hlam, p519_0]
                              · have p519_0 := h519c.1
                                have p519_1 := h519c.2.1
                                have p519_2 := h519c.2.2.1
                                have p519_3 := h519c.2.2.2
                                linarith only [hlam, p519_0]
                            · linarith only [h0, h463, h512, h518, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h460, h463, h512, h514, h516, h517, hc34, hlam, hphi, ht23, u2ehi4]
                        · linarith only [h456, h459, h516, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h457, h460, h463, h512, h513, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h456, h459, h461, h512, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h458, h462, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h456, h461, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h552 | h552
            · rcases m.htr 1 2 5 (by decide) (by decide) with h553 | h553
              · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
                · rcases m.htr 1 3 5 (by decide) (by decide) with h555 | h555
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h556 | h556
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h557 | h557
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h558 | h558
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h559 | h559
                          · linarith only [h457, h460, h559, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h561 | h561
                            · linarith only [h456, h457, h460, h557, h561, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                            · rcases h5bigk with h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [hlam, p563_0]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h0, hlam, p563_1]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [hc25, hlam, hphi, ht0b, ht5b, p563_1, u0elo4]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h456, h459, h561, hc34, hlam, hphi, ht0b, ht45, ht5b, p563_1, u0elo1]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h460, hlam, p563_1]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p563_1]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [hlam, p563_0]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h553, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p563_1, u2ehi4]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                rcases p563_3 (m.d 0 5) (by simp) with h572 | h572
                                · linarith only [h0, h572, hlam]
                                · linarith only [h459, h572, hlam]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h457, h460, h552, h554, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p563_1, u2ehi3]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h458, hlam, p563_1]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h553, hlam, p563_1]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [hlam, p563_0]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h458, h561, hc34, hlam, hphi, ht0b, ht45, ht5b, p563_1, u0elo1]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h559, hlam, p563_1]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h459, hlam, p563_0]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h555, hlam, p563_0]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h558, hlam, p563_0]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [hlam, p563_0]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h561, hlam, p563_1]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h458, hc45, hlam, hphi, ht23, ht34, p563_1, u2ehi4]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h556, hlam, p563_0]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h552, h554, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p563_1, u2ehi4]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [h552, h554, h556, h561, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p563_1]
                              · have p563_0 := h563c.1
                                have p563_1 := h563c.2.1
                                have p563_2 := h563c.2.2.1
                                have p563_3 := h563c.2.2.2
                                linarith only [hlam, p563_0]
                        · linarith only [h456, h459, h558, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h592 | h592
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h593 | h593
                          · linarith only [h457, h460, h593, hlam]
                          · linarith only [h557, h592, h593, hlam]
                        · linarith only [h456, h459, h592, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h597 | h597
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h598 | h598
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h599 | h599
                          · linarith only [h0, h457, h460, h556, h599, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h601 | h601
                            · linarith only [h456, h460, h597, h601, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases h5bigk with h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [hlam, p603_0]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h0, hlam, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [hc25, hlam, hphi, ht0b, ht5b, p603_1, u0elo4]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h456, h459, h601, hc34, hlam, hphi, ht0b, ht45, ht5b, p603_1, u0elo1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h460, hlam, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [hlam, p603_0]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h553, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p603_1, u2ehi4]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h556, h601, hc34, hc45, hlam, hphi, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h556, hlam, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h458, hlam, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h553, hlam, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [hlam, p603_0]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h458, h601, hc34, hlam, hphi, ht0b, ht45, ht5b, p603_1, u0elo1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h599, hlam, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h459, hlam, p603_0]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h555, hlam, p603_0]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h598, hlam, p603_0]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [hlam, p603_0]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h601, hlam, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h458, hc45, hlam, hphi, ht23, ht34, p603_1, u2ehi4]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [hc45, hlam, hphi, ht23, ht34, p603_1, u2ehi4]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [h601, hc34, hc45, hlam, hphi, p603_1]
                              · have p603_0 := h603c.1
                                have p603_1 := h603c.2.1
                                have p603_2 := h603c.2.2.1
                                have p603_3 := h603c.2.2.2
                                linarith only [hlam, p603_0]
                        · linarith only [h456, h459, h598, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h554, h556, h597, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h456, h459, h554, h555, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h632 | h632
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h633 | h633
                    · linarith only [h457, h460, h554, h633, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h554, h632, h633, hlam]
                  · linarith only [h456, h459, h552, h632, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h552, h553, hc25, hlam, hphi, u2ehi2]
            · linarith only [h456, h552, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h639 | h639
          · rcases m.htr 1 2 3 (by decide) (by decide) with h640 | h640
            · rcases m.htr 1 2 5 (by decide) (by decide) with h641 | h641
              · rcases m.htr 1 3 4 (by decide) (by decide) with h642 | h642
                · rcases m.htr 1 3 5 (by decide) (by decide) with h643 | h643
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h644 | h644
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h645 | h645
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h646 | h646
                        · linarith only [h456, h459, h646, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h648 | h648
                          · linarith only [h645, h646, h648, hlam]
                          · linarith only [h639, h648, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h651 | h651
                        · linarith only [h456, h459, h651, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h653 | h653
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h654 | h654
                            · rcases h5bigk with h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h0, hlam, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h651, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p655_1, u0elo4]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h459, hlam, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hc45, hlam, hphi, ht0b, ht5b, p655_1, u0elo4]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h641, h651, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p655_1, u2ehi2]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h456, h459, h643, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p655_1, u2ehi2]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                rcases p655_3 (m.d 0 5) (by simp) with h665 | h665
                                · linarith only [h0, h665, hlam]
                                · linarith only [h639, h665, hlam]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h458, hlam, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h641, hlam, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h651, hlam, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h458, hc45, hlam, hphi, ht0b, ht5b, p655_1, u0elo4]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h0, h654, hc01, hc34, hlam, hphi, ht12, ht23, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h643, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h640, h642, h654, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h640, h642, h654, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p655_1]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h639, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h644, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h653, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [h654, hlam, p655_0]
                              · have p655_0 := h655c.1
                                have p655_1 := h655c.2.1
                                have p655_2 := h655c.2.2.1
                                have p655_3 := h655c.2.2.2
                                linarith only [hlam, p655_0]
                            · linarith only [h457, h639, h645, h654, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                          · linarith only [h457, h639, h653, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                    · linarith only [h456, h457, h459, h639, h643, h644, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h686 | h686
                    · linarith only [h642, h643, h686, hlam]
                    · linarith only [h0, h639, h686, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h689 | h689
                  · linarith only [h456, h459, h642, h689, hc34, hlam, hphi, ht23, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h691 | h691
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h692 | h692
                      · linarith only [h456, h642, h692, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h694 | h694
                        · linarith only [h456, h459, h694, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h696 | h696
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h697 | h697
                            · rcases h5bigk with h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [hlam, p698_0]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h0, hlam, p698_1]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h694, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p698_1, u0elo4, u2ehi2]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h459, hlam, p698_1]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [hc45, hlam, hphi, ht0b, ht5b, p698_1, u0elo4]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p698_1]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [hlam, p698_0]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h641, h694, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p698_1, u2ehi2]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h689, hlam, p698_1]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                rcases p698_3 (m.d 0 5) (by simp) with h708 | h708
                                · linarith only [h0, h708, hlam]
                                · linarith only [h639, h708, hlam]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h458, hlam, p698_1]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h641, hlam, p698_1]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [hlam, p698_0]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h694, hlam, p698_1]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h458, hc45, hlam, hphi, ht0b, ht5b, p698_1, u0elo4]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h0, h697, hc01, hc34, hlam, hphi, ht12, ht23, p698_1]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h0, h697, hc01, hc34, hlam, hphi, ht12, ht23, p698_1]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h697, hc34, hlam, hphi, ht23, p698_1, u2ehi4]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [hlam, p698_0]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                rcases p698_3 (m.d 0 5) (by simp) with h720 | h720
                                · linarith only [h459, h720, hlam]
                                · linarith only [h639, h720, hlam]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h639, hlam, p698_0]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h691, hlam, p698_0]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h696, hlam, p698_0]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [h697, hlam, p698_0]
                              · have p698_0 := h698c.1
                                have p698_1 := h698c.2.1
                                have p698_2 := h698c.2.2.1
                                have p698_3 := h698c.2.2.2
                                linarith only [hlam, p698_0]
                            · linarith only [h639, h640, h642, h697, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi2]
                          · linarith only [h457, h639, h696, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                    · linarith only [h457, h639, h640, h642, h691, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h458, h641, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h456, h640, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h733 | h733
            · rcases m.htr 1 2 5 (by decide) (by decide) with h734 | h734
              · rcases m.htr 1 3 4 (by decide) (by decide) with h735 | h735
                · rcases m.htr 1 3 5 (by decide) (by decide) with h736 | h736
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h737 | h737
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h738 | h738
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h739 | h739
                        · linarith only [h456, h459, h739, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h741 | h741
                          · linarith only [h457, h639, h741, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h743 | h743
                            · linarith only [h456, h457, h459, h639, h733, h736, h738, h743, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases h5bigk with h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [hlam, p745_0]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h0, hlam, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h459, h733, h735, h737, h743, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h459, hlam, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h639, hlam, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [hlam, p745_0]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h734, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p745_1, u2ehi4]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h459, h733, h736, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h457, h639, h733, h735, h737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p745_1, u2ehi3]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h458, hlam, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h734, hlam, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [hlam, p745_0]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h739, hlam, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h741, hlam, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h456, h459, hc35, hlam, hphi, ht23, p745_1, u2ehi2]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h736, hlam, p745_0]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h733, h736, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p745_1, u2ehi4]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [hlam, p745_0]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h743, hlam, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h456, h459, h738, hc45, hlam, hphi, ht23, ht34, p745_1, u2ehi3]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h737, hlam, p745_0]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h733, h735, h737, h738, h739, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p745_1, u2ehi3]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [h733, h735, h737, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p745_1]
                              · have p745_0 := h745c.1
                                have p745_1 := h745c.2.1
                                have p745_2 := h745c.2.2.1
                                have p745_3 := h745c.2.2.2
                                linarith only [hlam, p745_0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h771 | h771
                        · linarith only [h456, h459, h771, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h773 | h773
                          · linarith only [h457, h639, h773, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h775 | h775
                            · linarith only [h457, h639, h738, h775, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h738, h775, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h778 | h778
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h779 | h779
                        · linarith only [h456, h459, h779, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h781 | h781
                          · linarith only [h0, h456, h459, h737, h778, h781, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h783 | h783
                            · linarith only [h456, h459, h736, h737, h778, h783, hlam]
                            · rcases h5bigk with h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [hlam, p785_0]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h0, hlam, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h779, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p785_1, u0elo4]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h459, hlam, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h639, hlam, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h0, h737, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [hlam, p785_0]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h737, h778, h779, hc45, hlam, hphi, ht23, ht34, p785_1, u2ehi3]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h456, h459, h737, h778, hc45, hlam, hphi, ht23, ht34, p785_1, u2ehi3]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h737, hlam, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h458, hlam, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h734, hlam, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [hlam, p785_0]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h779, hlam, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h781, hlam, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h458, h733, h736, h778, h779, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p785_1, u2ehi3]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h736, hlam, p785_0]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h733, h736, h778, h779, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p785_1, u2ehi3]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [hlam, p785_0]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h783, hlam, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h458, h778, h779, hc45, hlam, hphi, ht23, ht34, p785_1, u2ehi3]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p785_1]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h778, h779, hc45, hlam, hphi, ht23, ht34, p785_1, u2ehi3]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [h456, h459, h778, hc45, hlam, hphi, ht23, ht34, p785_1, u2ehi3]
                              · have p785_0 := h785c.1
                                have p785_1 := h785c.2.1
                                have p785_2 := h785c.2.2.1
                                have p785_3 := h785c.2.2.2
                                linarith only [hlam, p785_0]
                      · linarith only [h735, h737, h778, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h812 | h812
                    · linarith only [h457, h639, h735, h736, h812, hc35, hlam, hphi, ht23, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h814 | h814
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h815 | h815
                        · linarith only [h456, h736, h815, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h817 | h817
                          · linarith only [h457, h639, h817, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h819 | h819
                            · linarith only [h457, h458, h639, h814, h815, h819, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                            · rcases h5bigk with h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [hlam, p821_0]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h0, hlam, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h815, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p821_1, u0elo4]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h459, hlam, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h639, hlam, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [hlam, p821_0]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h736, h815, h819, hc45, hlam, hphi, ht23, ht34, p821_1, u2ehi2]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h736, hlam, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h812, hlam, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h458, hlam, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h734, hlam, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [hlam, p821_0]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h815, hlam, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h817, hlam, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h458, h815, h819, hc45, hlam, hphi, ht23, ht34, p821_1, u2ehi2]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h0, h819, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h814, h815, h819, hc45, hlam, hphi, ht23, ht34, p821_1, u2ehi3]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [hlam, p821_0]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h819, hlam, p821_1]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h458, h814, h815, hc45, hlam, hphi, ht23, ht34, p821_1, u2ehi3]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h0, h458, h814, h815, hc45, hlam, hphi, ht23, ht34, p821_1, u2ehi3]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h814, h815, hc45, hlam, hphi, ht23, ht34, p821_1, u2ehi3]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [h456, h459, h814, hc45, hlam, hphi, ht23, ht34, p821_1, u2ehi3]
                              · have p821_0 := h821c.1
                                have p821_1 := h821c.2.1
                                have p821_2 := h821c.2.2.1
                                have p821_3 := h821c.2.2.2
                                linarith only [hlam, p821_0]
                      · linarith only [h735, h736, h814, hc35, hlam, hphi, ht23, u2ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h848 | h848
                  · linarith only [h456, h459, h735, h848, hc34, hlam, hphi, ht23, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h850 | h850
                    · linarith only [h457, h639, h735, h850, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h852 | h852
                      · linarith only [h456, h735, h852, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h854 | h854
                        · linarith only [h456, h459, h854, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h856 | h856
                          · linarith only [h457, h639, h856, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h858 | h858
                            · linarith only [h457, h639, h852, h858, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h733, h735, h858, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h458, h734, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h456, h459, h733, hc35, hlam, hphi, ht23, u2ehi1]
      · linarith only [h456, h458, hc25, hlam, hphi, u2ehi2]
    · linarith only [h456, h457, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h865 | h865
    · linarith only [h456, h865, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h867 | h867
      · linarith only [h456, h867, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h869 | h869
        · rcases m.htr 0 4 5 (by decide) (by decide) with h870 | h870
          · rcases m.htr 1 2 3 (by decide) (by decide) with h871 | h871
            · rcases m.htr 1 2 5 (by decide) (by decide) with h872 | h872
              · rcases m.htr 1 3 4 (by decide) (by decide) with h873 | h873
                · rcases m.htr 1 3 5 (by decide) (by decide) with h874 | h874
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h875 | h875
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h876 | h876
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h877 | h877
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h878 | h878
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h879 | h879
                            · rcases h5bigk with h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h0, hlam, p880_1]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h867, hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h869, hc35, hlam, hphi, ht0b, ht5b, p880_1, u0elo2]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h865, h870, h871, h876, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p880_1]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h0, h873, h875, hc01, hc13, hlam, hphi, p880_1]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h871, h873, h875, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p880_1, u2ehi4]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                rcases p880_3 (m.d 0 5) (by simp) with h889 | h889
                                · linarith only [h0, h889, hlam]
                                · linarith only [h869, h889, hlam]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                rcases p880_3 (m.d 0 5) (by simp) with h892 | h892
                                · linarith only [h0, h892, hlam]
                                · linarith only [h870, h892, hlam]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h867, hc25, hlam, hphi, p880_1, u2ehi0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h872, hlam, p880_1]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h871, h877, h879, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p880_1]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h871, h876, h878, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p880_1]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h869, hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h874, hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h877, hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h456, h869, h871, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p880_1]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h870, hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h875, hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h878, hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [h879, hlam, p880_0]
                              · have p880_0 := h880c.1
                                have p880_1 := h880c.2.1
                                have p880_2 := h880c.2.2.1
                                have p880_3 := h880c.2.2.2
                                linarith only [hlam, p880_0]
                            · rcases h5bigk with h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c | h910c
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h0, hlam, p910_1]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h867, hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [hc35, hlam, hphi, ht0b, ht5b, p910_1, u0elo4]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h867, h871, h876, h878, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p910_1]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h0, h871, h873, h875, hc01, hc12, hlam, hphi, p910_1]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h871, h873, h875, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p910_1, u2ehi4]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                rcases p910_3 (m.d 0 5) (by simp) with h919 | h919
                                · linarith only [h0, h919, hlam]
                                · linarith only [h869, h919, hlam]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h871, h873, h875, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p910_1]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h867, hc25, hlam, hphi, p910_1, u2ehi0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h872, hlam, p910_1]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h871, h877, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p910_1]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h871, h876, h878, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p910_1]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h869, hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h874, hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h877, hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h879, hlam, p910_1]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h870, hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h875, hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h878, hlam, p910_0]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [h879, hc34, hc45, hlam, hphi, p910_1]
                              · have p910_0 := h910c.1
                                have p910_1 := h910c.2.1
                                have p910_2 := h910c.2.2.1
                                have p910_3 := h910c.2.2.2
                                linarith only [hlam, p910_0]
                          · linarith only [h865, h870, h878, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi0]
                        · linarith only [h456, h877, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h456, h876, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h870, h875, hlam]
                  · linarith only [h456, h869, h871, h874, hlam]
                · linarith only [h456, h871, h873, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h456, h871, h872, hc25, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h945 | h945
              · linarith only [h871, h945, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h947 | h947
                · rcases m.htr 1 3 5 (by decide) (by decide) with h948 | h948
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h949 | h949
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h950 | h950
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h951 | h951
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h952 | h952
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h953 | h953
                            · rcases h5bigk with h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h0, hlam, p954_1]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h867, hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [hc35, hlam, hphi, ht0b, ht5b, p954_1, u0elo4]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [hc45, hlam, hphi, ht0b, ht5b, p954_1, u0elo4]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h0, h945, hc01, hc25, hlam, hphi, ht12, p954_1]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h945, hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                rcases p954_3 (m.d 0 5) (by simp) with h963 | h963
                                · linarith only [h0, h963, hlam]
                                · linarith only [h869, h963, hlam]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                rcases p954_3 (m.d 0 5) (by simp) with h966 | h966
                                · linarith only [h0, h966, hlam]
                                · linarith only [h870, h966, hlam]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h867, h950, h952, hc23, hlam, hphi, p954_1, u2ehi0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h0, h950, h952, hc01, hc23, hlam, hphi, ht12, p954_1]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                rcases p954_3 (m.d 0 5) (by simp) with h972 | h972
                                · linarith only [h867, h972, hlam]
                                · linarith only [h869, h972, hlam]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                rcases p954_3 (m.d 0 5) (by simp) with h975 | h975
                                · linarith only [h867, h975, hlam]
                                · linarith only [h870, h975, hlam]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h869, hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h948, hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h951, hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h869, hc45, hlam, hphi, ht0b, ht5b, p954_1, u0elo2]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h870, hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h949, hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h952, hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [h953, hlam, p954_0]
                              · have p954_0 := h954c.1
                                have p954_1 := h954c.2.1
                                have p954_2 := h954c.2.2.1
                                have p954_3 := h954c.2.2.2
                                linarith only [hlam, p954_0]
                            · rcases h5bigk with h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h867, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hc35, hlam, hphi, ht0b, ht5b, p988_1, u0elo4]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h869, h953, hc34, hlam, hphi, ht0b, ht45, ht5b, p988_1, u0elo2]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h945, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                rcases p988_3 (m.d 0 5) (by simp) with h997 | h997
                                · linarith only [h0, h997, hlam]
                                · linarith only [h869, h997, hlam]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h945, h950, h952, h953, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h867, h950, h952, hc23, hlam, hphi, p988_1, u2ehi0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, h950, h952, hc01, hc23, hlam, hphi, ht12, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                rcases p988_3 (m.d 0 5) (by simp) with h1004 | h1004
                                · linarith only [h1004, h867, hlam]
                                · linarith only [h1004, h869, hlam]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h950, h952, h953, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h869, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h948, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h951, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h953, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h870, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h949, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h952, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h953, hc34, hc45, hlam, hphi, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                          · linarith only [h865, h870, h952, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi0]
                        · linarith only [h871, h951, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h456, h950, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h870, h949, hlam]
                  · linarith only [h869, h871, h948, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1023 | h1023
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1024 | h1024
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1025 | h1025
                      · linarith only [h0, h1023, h1025, h947, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h1025, h456, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h1023, h1024, h870, h947, hlam]
                  · linarith only [h1023, h869, h871, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1030 | h1030
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1031 | h1031
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1032 | h1032
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1033 | h1033
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1034 | h1034
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1035 | h1035
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1036 | h1036
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1037 | h1037
                          · linarith only [h1030, h1035, h1037, h865, h870, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1037, h865, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1036, h456, h869, hlam]
                      · linarith only [h1035, h456, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1042 | h1042
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1043 | h1043
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1044 | h1044
                          · linarith only [h1044, h865, h870, hc24, hlam, hphi, u2ehi0]
                          · linarith only [h1044, h865, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1043, h456, h869, hlam]
                      · linarith only [h1042, h456, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1032, h1033, h869, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h1030, h1032, h456, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h1030, h1031, h456, hc25, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1052 | h1052
              · linarith only [h1030, h1052, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1054 | h1054
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1055 | h1055
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1056 | h1056
                    · linarith only [h1030, h1054, h1056, h865, h870, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1058 | h1058
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1059 | h1059
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1060 | h1060
                          · linarith only [h1060, h865, h870, hc24, hlam, hphi, u2ehi0]
                          · linarith only [h1060, h865, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1059, h869, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                      · linarith only [h1058, h456, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1054, h1055, h869, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1066 | h1066
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1067 | h1067
                    · linarith only [h1054, h1067, h865, h870, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1054, h1066, h1067, hlam]
                  · linarith only [h1030, h1066, h869, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1071 | h1071
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1072 | h1072
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1073 | h1073
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1074 | h1074
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1075 | h1075
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1076 | h1076
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1077 | h1077
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1078 | h1078
                        · linarith only [h1072, h1078, h456, h869, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1075, h1078, h456, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1077, h456, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1071, h1075, h1076, h456, h869, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi0]
                  · linarith only [h1072, h1075, h456, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1072, h1074, h456, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h1072, h1073, h456, hc25, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1086 | h1086
              · linarith only [h1072, h1086, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1088 | h1088
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1089 | h1089
                  · linarith only [h1072, h1089, h456, h869, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1091 | h1091
                    · linarith only [h1088, h1089, h1091, hlam]
                    · linarith only [h0, h1071, h1091, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1094 | h1094
                  · linarith only [h1088, h1094, h456, h869, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1096 | h1096
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1097 | h1097
                      · linarith only [h1072, h1088, h1097, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h1097, h456, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1071, h1072, h1088, h1096, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1101 | h1101
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1102 | h1102
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1103 | h1103
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1104 | h1104
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1105 | h1105
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1106 | h1106
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1107 | h1107
                        · linarith only [h1107, h456, h869, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1107, h456, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1106, h456, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1111 | h1111
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1112 | h1112
                        · linarith only [h1112, h456, h869, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1112, h456, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1103, h1105, h1111, h456, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h1101, h1104, h456, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1101, h1103, h456, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h1101, h1102, h456, hc25, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1119 | h1119
              · linarith only [h1101, h1119, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1121 | h1121
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1122 | h1122
                  · linarith only [h1101, h1122, h456, h869, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1124 | h1124
                    · linarith only [h1071, h1121, h1122, h1124, h865, hc35, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1126 | h1126
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1127 | h1127
                        · linarith only [h1127, h456, h869, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1127, h456, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1121, h1122, h1126, h456, hc35, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1131 | h1131
                  · linarith only [h1121, h1131, h456, h869, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1133 | h1133
                    · linarith only [h1071, h1121, h1133, h865, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1135 | h1135
                      · linarith only [h1101, h1121, h1135, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h1135, h456, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_10_12_25_L_0_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_25_L_0_L_R_H_I_x0 m hb0 hb2 hb5 h0
  · exact r1l7_10_12_25_L_0_L_R_H_I_x1 m hb0 hb2 hb5 h0

end R2N4
