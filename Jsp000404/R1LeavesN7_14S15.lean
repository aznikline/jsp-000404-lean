import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8986000 in
set_option maxHeartbeats 8986000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s6 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  rcases m.htr 0 1 5 (by decide) (by decide) with h7494 | h7494
  · rcases m.htr 0 2 3 (by decide) (by decide) with h7495 | h7495
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7496 | h7496
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7497 | h7497
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7498 | h7498
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7499 | h7499
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7500 | h7500
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7501 | h7501
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7502 | h7502
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7503 | h7503
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7504 | h7504
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7505 | h7505
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7506 | h7506
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7507 | h7507
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7508 | h7508
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7509 | h7509
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7510 | h7510
                                  · linarith only [h7495, h7507, h7510, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h7495, h7507, h7509, h7510, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7513 | h7513
                                  · linarith only [h7507, h7509, h7513, hlam]
                                  · rcases h0bigk with h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c | h7515c
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [hlam, p7515_0]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h0, hlam, p7515_1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h4610, hlam, p7515_0]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h6681, hlam, p7515_1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7494, h7506, h7507, h7509, hc34, hlam, hphi, ht0b, ht45, ht5b, p7515_1, u0elo0]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7494, h7506, h7507, h7509, hc34, hlam, hphi, ht0b, ht45, ht5b, p7515_1, u0elo1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [hlam, p7515_0]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h4610, h7494, h7506, h7507, h7509, hc34, hlam, hphi, ht0b, ht45, ht5b, p7515_1, u0elo1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h6681, h7494, h7506, h7507, h7509, hc34, hlam, hphi, ht0b, ht45, ht5b, p7515_1, u0elo1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7494, h7506, h7507, h7509, hc34, hlam, hphi, ht0b, ht45, ht5b, p7515_1, u0elo1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7494, h7506, h7507, h7509, hc34, hlam, hphi, ht0b, ht45, ht5b, p7515_1, u0elo2]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7495, hlam, p7515_1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [hlam, p7515_0]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h6681, h7494, h7495, h7506, h7507, h7509, hc34, hlam, hphi, ht0b, ht45, ht5b, p7515_1, u0elo1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7494, h7495, h7506, h7507, h7509, hc34, hlam, hphi, ht0b, ht45, ht5b, p7515_1, u0elo1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7494, h7506, h7507, h7509, hc34, hlam, hphi, ht0b, ht45, ht5b, p7515_1, u0elo3]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7496, hlam, p7515_0]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7498, hlam, p7515_0]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [hlam, p7515_0]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7494, h7495, h7498, h7506, h7507, h7509, hc34, hlam, hphi, ht0b, ht45, ht5b, p7515_1, u0elo1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7494, hlam, p7515_0]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7497, hlam, p7515_1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7499, hlam, p7515_0]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [h7500, hlam, p7515_1]
                                    · have p7515_0 := h7515c.1
                                      have p7515_1 := h7515c.2.1
                                      have p7515_2 := h7515c.2.2.1
                                      have p7515_3 := h7515c.2.2.2
                                      linarith only [hlam, p7515_0]
                              · linarith only [h6681, h7494, h7501, h7504, h7505, h7507, h7508, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7542 | h7542
                              · linarith only [h7495, h7498, h7507, h7542, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7544 | h7544
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7545 | h7545
                                  · rcases h0bigk with h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [hlam, p7546_0]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h0, hlam, p7546_1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h4610, hlam, p7546_0]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h6681, hlam, p7546_1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h6681, h7494, h7501, h7504, h7505, h7542, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7546_1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7494, h7505, h7542, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7546_1, u0elo1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [hlam, p7546_0]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7498, hc34, hlam, hphi, ht0b, ht45, ht5b, p7546_1, u0elo1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h6681, h7494, h7505, h7542, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7546_1, u0elo1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7494, h7505, h7542, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7546_1, u0elo1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7494, h7505, h7542, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7546_1, u0elo2]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7495, hlam, p7546_1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [hlam, p7546_0]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h6681, h7494, h7495, h7505, h7542, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7546_1, u0elo1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7494, h7495, h7505, h7542, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7546_1, u0elo1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7494, h7505, h7542, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7546_1, u0elo3]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7496, hlam, p7546_0]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7498, hlam, p7546_0]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [hlam, p7546_0]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7494, h7495, h7498, h7505, h7542, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7546_1, u0elo1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7494, hlam, p7546_0]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7497, hlam, p7546_1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7499, hlam, p7546_0]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [h7500, hlam, p7546_1]
                                    · have p7546_0 := h7546c.1
                                      have p7546_1 := h7546c.2.1
                                      have p7546_2 := h7546c.2.2.1
                                      have p7546_3 := h7546c.2.2.2
                                      linarith only [hlam, p7546_0]
                                  · linarith only [h7496, h7507, h7544, h7545, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7573 | h7573
                                  · linarith only [h7495, h7498, h7507, h7544, h7573, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · linarith only [h7494, h7506, h7507, h7573, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h6681, h7495, h7498, h7500, h7506, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h6681, h7495, h7499, h7504, h7505, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h4610, h7498, h7504, hlam]
                    · linarith only [h0, h7497, h7503, hlam]
                  · linarith only [h0, h7496, h7502, hlam]
                · linarith only [h0, h7495, h7501, hlam]
              · linarith only [h6681, h7494, h7500, hlam]
            · linarith only [h4610, h7494, h7499, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7584 | h7584
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7585 | h7585
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7586 | h7586
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7587 | h7587
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7588 | h7588
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7589 | h7589
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7590 | h7590
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7591 | h7591
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7592 | h7592
                            · linarith only [h4610, h7495, h7498, h7592, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7594 | h7594
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7595 | h7595
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7596 | h7596
                                  · rcases h0bigk with h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c | h7597c
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [hlam, p7597_0]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h0, hlam, p7597_1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h4610, hlam, p7597_0]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h6681, hlam, p7597_1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h4610, h7498, h7586, h7589, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7597_1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7494, hc15, hlam, hphi, ht0b, ht5b, p7597_1, u0elo1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [hlam, p7597_0]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h4610, h7494, h7588, h7594, h7596, hc45, hlam, hphi, ht0b, ht5b, p7597_1, u0elo1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h4610, h7494, h7498, h7588, h7594, h7596, hc45, hlam, hphi, ht0b, ht5b, p7597_1, u0elo1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      rcases p7597_3 (m.d 0 1) (by simp) with h7607 | h7607
                                      · linarith only [h0, h7607, hlam]
                                      · linarith only [h7494, h7607, hlam]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7494, h7498, h7586, h7588, h7589, h7594, h7596, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7597_1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7495, hlam, p7597_1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [hlam, p7597_0]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7498, hlam, p7597_1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7494, h7498, h7586, h7588, h7589, h7594, h7596, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7597_1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7494, h7588, h7594, h7596, hc45, hlam, hphi, ht0b, ht5b, p7597_1, u0elo3]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7496, hlam, p7597_0]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h4610, h7494, h7498, h7586, h7588, h7589, h7594, h7596, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7597_1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [hlam, p7597_0]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      rcases p7597_3 (m.d 0 1) (by simp) with h7619 | h7619
                                      · linarith only [h6681, h7619, hlam]
                                      · linarith only [h7494, h7619, hlam]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7494, hlam, p7597_0]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7497, hlam, p7597_1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7584, hlam, p7597_0]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [h7585, hlam, p7597_1]
                                    · have p7597_0 := h7597c.1
                                      have p7597_1 := h7597c.2.1
                                      have p7597_2 := h7597c.2.2.1
                                      have p7597_3 := h7597c.2.2.2
                                      linarith only [hlam, p7597_0]
                                  · linarith only [h4610, h7494, h7498, h7585, h7588, h7594, h7596, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                                · linarith only [h4610, h7494, h7498, h7586, h7589, h7591, h7595, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7498, h7584, h7586, h7589, h7594, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7498, h7585, h7589, h7591, hlam]
                        · linarith only [h4610, h7498, h7589, h7590, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7632 | h7632
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7633 | h7633
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7634 | h7634
                            · linarith only [h4610, h7589, h7634, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7636 | h7636
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7637 | h7637
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7638 | h7638
                                  · rcases h0bigk with h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c | h7639c
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [hlam, p7639_0]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h0, hlam, p7639_1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h4610, hlam, p7639_0]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h6681, hlam, p7639_1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h4610, h7494, h7588, h7589, h7636, h7638, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7639_1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h7494, h7588, h7636, h7638, hc45, hlam, hphi, ht0b, ht5b, p7639_1, u0elo1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [hlam, p7639_0]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h4610, h7494, h7588, h7636, h7638, hc45, hlam, hphi, ht0b, ht5b, p7639_1, u0elo1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h6681, h7494, h7588, h7636, h7638, hc45, hlam, hphi, ht0b, ht5b, p7639_1, u0elo1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      rcases p7639_3 (m.d 0 1) (by simp) with h7649 | h7649
                                      · linarith only [h0, h7649, hlam]
                                      · linarith only [h7494, h7649, hlam]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h7494, h7588, h7636, h7638, hc45, hlam, hphi, ht0b, ht5b, p7639_1, u0elo2]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h7495, hlam, p7639_1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [hlam, p7639_0]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h7498, hlam, p7639_1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      rcases p7639_3 (m.d 0 1) (by simp) with h7656 | h7656
                                      · linarith only [h4610, h7656, hlam]
                                      · linarith only [h7494, h7656, hlam]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h7494, h7496, h7588, h7636, h7638, hc45, hlam, hphi, ht0b, ht5b, p7639_1, u0elo1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h7496, hlam, p7639_0]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h4610, h7494, h7496, h7588, h7636, h7638, hc45, hlam, hphi, ht0b, ht5b, p7639_1, u0elo1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [hlam, p7639_0]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      rcases p7639_3 (m.d 0 1) (by simp) with h7663 | h7663
                                      · linarith only [h6681, h7663, hlam]
                                      · linarith only [h7494, h7663, hlam]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h7494, hlam, p7639_0]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h7497, hlam, p7639_1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h7584, hlam, p7639_0]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [h7585, hlam, p7639_1]
                                    · have p7639_0 := h7639c.1
                                      have p7639_1 := h7639c.2.1
                                      have p7639_2 := h7639c.2.2.1
                                      have p7639_3 := h7639c.2.2.2
                                      linarith only [hlam, p7639_0]
                                  · linarith only [h4610, h7589, h7638, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h4610, h7494, h7589, h7633, h7634, h7637, hc23, hc34, hlam, hphi]
                              · linarith only [h4610, h7584, h7589, h7636, hc23, hc34, hlam, hphi]
                          · linarith only [h6681, h7585, h7633, hlam]
                        · linarith only [h4610, h7584, h7632, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h7497, h7588, hlam]
                  · linarith only [h0, h7496, h7587, hlam]
                · linarith only [h0, h7495, h7586, hlam]
              · linarith only [h4610, h7494, h7498, h7585, hlam]
            · linarith only [h4610, h7494, h7584, hlam]
        · linarith only [h0, h7494, h7497, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7682 | h7682
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7683 | h7683
          · linarith only [h7495, h7496, h7683, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7685 | h7685
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7686 | h7686
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7687 | h7687
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7688 | h7688
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7689 | h7689
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7690 | h7690
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7691 | h7691
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7692 | h7692
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7693 | h7693
                            · linarith only [h4610, h7494, h7495, h7683, h7689, h7693, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7695 | h7695
                              · linarith only [h7495, h7496, h7687, h7690, h7693, h7695, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h7495, h7496, h7685, h7687, h7690, h7693, h7695, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7683, h7686, h7690, h7692, hlam]
                        · linarith only [h7495, h7496, h7683, h7685, h7688, h7690, h7691, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7700 | h7700
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7701 | h7701
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7702 | h7702
                            · linarith only [h4610, h7494, h7689, h7690, h7702, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7704 | h7704
                              · linarith only [h7495, h7496, h7688, h7704, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h7495, h7496, h7685, h7688, h7704, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7495, h7496, h7688, h7701, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h7495, h7496, h7685, h7688, h7700, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h7496, h7688, h7689, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7710 | h7710
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7711 | h7711
                      · linarith only [h4610, h7494, h7683, h7687, h7688, h7710, h7711, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7713 | h7713
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7714 | h7714
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7715 | h7715
                            · linarith only [h7495, h7711, h7715, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7717 | h7717
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7718 | h7718
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7719 | h7719
                                  · rcases h0bigk with h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c | h7720c
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [hlam, p7720_0]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h0, hlam, p7720_1]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h4610, hlam, p7720_0]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h6681, hlam, p7720_1]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h0, h7688, h7715, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7720_1]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h0, h7688, h7715, hc01, hc34, hlam, hphi, ht12, ht23, p7720_1]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [hlam, p7720_0]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h0, h7688, h7715, hc03, hc34, hlam, hphi, p7720_1]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h7496, hlam, p7720_1]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      rcases p7720_3 (m.d 0 1) (by simp) with h7730 | h7730
                                      · linarith only [h0, h7730, hlam]
                                      · linarith only [h7494, h7730, hlam]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h7494, h7710, h7717, h7719, hc45, hlam, hphi, ht0b, ht5b, p7720_1, u0elo2]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h7495, hlam, p7720_1]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [hlam, p7720_0]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h7683, hlam, p7720_1]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      rcases p7720_3 (m.d 0 1) (by simp) with h7737 | h7737
                                      · linarith only [h4610, h7737, hlam]
                                      · linarith only [h7494, h7737, hlam]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h7494, h7710, h7717, h7719, hc45, hlam, hphi, ht0b, ht5b, p7720_1, u0elo3]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h7495, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7720_1, u0elo3]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h4610, h7494, h7710, h7717, h7719, hc45, hlam, hphi, ht0b, ht5b, p7720_1, u0elo3]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [hlam, p7720_0]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      rcases p7720_3 (m.d 0 1) (by simp) with h7744 | h7744
                                      · linarith only [h6681, h7744, hlam]
                                      · linarith only [h7494, h7744, hlam]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h7494, hlam, p7720_0]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h7682, hlam, p7720_1]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h7685, hlam, p7720_0]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [h7686, hlam, p7720_1]
                                    · have p7720_0 := h7720c.1
                                      have p7720_1 := h7720c.2.1
                                      have p7720_2 := h7720c.2.2.1
                                      have p7720_3 := h7720c.2.2.2
                                      linarith only [hlam, p7720_0]
                                  · linarith only [h4610, h7494, h7687, h7688, h7710, h7715, h7717, h7719, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h4610, h7494, h7687, h7688, h7714, h7718, hlam]
                              · linarith only [h4610, h7685, h7687, h7688, h7715, h7717, hc23, hc34, hlam, hphi]
                          · linarith only [h6681, h7686, h7714, hlam]
                        · linarith only [h0, h4610, h7495, h7685, h7688, h7713, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h7682, h7710, hlam]
                · linarith only [h0, h7495, h7687, hlam]
              · linarith only [h0, h7494, h7496, h7686, hlam]
            · linarith only [h4610, h7494, h7685, hlam]
        · linarith only [h4610, h7494, h7495, h7682, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7762 | h7762
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7763 | h7763
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7764 | h7764
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7765 | h7765
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7766 | h7766
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7767 | h7767
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7768 | h7768
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7769 | h7769
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7770 | h7770
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7771 | h7771
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7772 | h7772
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7773 | h7773
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7774 | h7774
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7775 | h7775
                                · linarith only [h7495, h7762, h7767, h7775, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h7495, h7762, h7766, h7767, h7775, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h6681, h7495, h7762, h7765, h7774, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h6681, h7495, h7762, h7764, h7773, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h6681, h7494, h7762, h7766, h7769, h7772, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h7495, h7765, h7767, h7771, hlam]
                      · linarith only [h4610, h7494, h7495, h7762, h7764, h7767, h7769, h7770, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h7495, h7767, h7769, hc02, hc25, hlam, hphi]
                  · linarith only [h7495, h7762, h7767, h7768, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7785 | h7785
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7786 | h7786
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7787 | h7787
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7788 | h7788
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7789 | h7789
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7790 | h7790
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7791 | h7791
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7792 | h7792
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7793 | h7793
                                  · rcases h0bigk with h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c | h7794c
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [hlam, p7794_0]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h0, hlam, p7794_1]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h4610, hlam, p7794_0]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h6681, hlam, p7794_1]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h6681, h7767, h7785, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7794_1]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h7494, hc15, hlam, hphi, ht0b, ht5b, p7794_1, u0elo1]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [hlam, p7794_0]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h7495, hlam, p7794_0]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h0, h6681, h7494, h7767, h7786, h7791, h7793, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7794_1]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      rcases p7794_3 (m.d 0 1) (by simp) with h7804 | h7804
                                      · linarith only [h0, h7804, hlam]
                                      · linarith only [h7494, h7804, hlam]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h7494, h7786, h7791, h7793, hc45, hlam, hphi, ht0b, ht5b, p7794_1, u0elo2]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h0, h7494, h7786, h7791, h7793, hc45, hlam, hphi, ht0b, ht5b, p7794_1, u0elo2]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [hlam, p7794_0]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h6681, h7494, h7786, h7791, h7793, hc45, hlam, hphi, ht0b, ht5b, p7794_1, u0elo2]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      rcases p7794_3 (m.d 0 1) (by simp) with h7811 | h7811
                                      · linarith only [h4610, h7811, hlam]
                                      · linarith only [h7494, h7811, hlam]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h7494, h7786, h7791, h7793, hc45, hlam, hphi, ht0b, ht5b, p7794_1, u0elo3]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h7762, hlam, p7794_0]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h7764, hlam, p7794_0]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [hlam, p7794_0]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      rcases p7794_3 (m.d 0 1) (by simp) with h7818 | h7818
                                      · linarith only [h6681, h7818, hlam]
                                      · linarith only [h7494, h7818, hlam]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h7494, hlam, p7794_0]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h7763, hlam, p7794_1]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h7765, hlam, p7794_0]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [h7766, hlam, p7794_1]
                                    · have p7794_0 := h7794c.1
                                      have p7794_1 := h7794c.2.1
                                      have p7794_2 := h7794c.2.2.1
                                      have p7794_3 := h7794c.2.2.2
                                      linarith only [hlam, p7794_0]
                                  · linarith only [h0, h7494, h7767, h7789, h7793, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h6681, h7494, h7767, h7785, h7789, h7792, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h6681, h7767, h7785, h7791, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h6681, h7767, h7785, h7790, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h6681, h7494, h7762, h7766, h7788, h7789, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h4610, h7765, h7788, hlam]
                      · linarith only [h0, h7494, h7764, h7767, h7786, h7787, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h7763, h7786, hlam]
                  · linarith only [h0, h7762, h7785, hlam]
              · linarith only [h6681, h7494, h7766, hlam]
            · linarith only [h0, h7494, h7495, h7765, hlam]
          · linarith only [h7495, h7762, h7764, hlam]
        · linarith only [h6681, h7494, h7762, h7763, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7839 | h7839
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7840 | h7840
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7841 | h7841
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7842 | h7842
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7843 | h7843
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7844 | h7844
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7845 | h7845
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7846 | h7846
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7847 | h7847
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7848 | h7848
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7849 | h7849
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7850 | h7850
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7851 | h7851
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7852 | h7852
                                  · rcases h0bigk with h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c | h7853c
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [hlam, p7853_0]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h0, hlam, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h4610, hlam, p7853_0]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h6681, hlam, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h0, h7762, h7843, h7849, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7762, h7843, h7849, hc01, hc12, hlam, hphi, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [hlam, p7853_0]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7495, hlam, p7853_0]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7762, hlam, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7494, h7762, h7843, h7845, h7849, h7850, h7852, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7494, h7845, h7850, h7852, hc45, hlam, hphi, ht0b, ht5b, p7853_1, u0elo2]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h0, h7494, h7495, h7843, h7845, h7850, h7852, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [hlam, p7853_0]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h0, h7494, h7495, h7762, h7843, h7845, h7850, h7852, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      rcases p7853_3 (m.d 0 1) (by simp) with h7868 | h7868
                                      · linarith only [h4610, h7868, hlam]
                                      · linarith only [h7494, h7868, hlam]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7494, h7845, h7850, h7852, hc45, hlam, hphi, ht0b, ht5b, p7853_1, u0elo3]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h0, h7494, h7762, h7843, h7845, h7849, h7850, h7852, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7840, hlam, p7853_0]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [hlam, p7853_0]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      rcases p7853_3 (m.d 0 1) (by simp) with h7875 | h7875
                                      · linarith only [h6681, h7875, hlam]
                                      · linarith only [h7494, h7875, hlam]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7494, hlam, p7853_0]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7839, hlam, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7841, hlam, p7853_0]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [h7842, hlam, p7853_1]
                                    · have p7853_0 := h7853c.1
                                      have p7853_1 := h7853c.2.1
                                      have p7853_2 := h7853c.2.2.1
                                      have p7853_3 := h7853c.2.2.2
                                      linarith only [hlam, p7853_0]
                                  · linarith only [h0, h7494, h7762, h7843, h7848, h7849, h7852, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h7494, h7762, h7848, h7851, hlam]
                              · linarith only [h7495, h7841, h7850, hlam]
                            · linarith only [h7495, h7840, h7849, hlam]
                          · linarith only [h6681, h7840, h7842, h7848, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h4610, h7841, h7847, hlam]
                      · linarith only [h7495, h7840, h7843, h7846, hlam]
                    · linarith only [h7762, h7839, h7845, hc12, hc24, hlam, hphi]
                  · linarith only [h7495, h7843, h7844, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7892 | h7892
                  · linarith only [h0, h7762, h7843, h7892, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7894 | h7894
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7895 | h7895
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7896 | h7896
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7897 | h7897
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7898 | h7898
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7899 | h7899
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7900 | h7900
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7901 | h7901
                                  · rcases h0bigk with h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c | h7902c
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [hlam, p7902_0]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h0, hlam, p7902_1]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h4610, hlam, p7902_0]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h6681, hlam, p7902_1]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h0, h7892, h7898, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7902_1]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h0, h7892, h7898, hc01, hc23, hlam, hphi, ht12, p7902_1]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [hlam, p7902_0]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h7495, hlam, p7902_0]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h7762, hlam, p7902_1]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      rcases p7902_3 (m.d 0 1) (by simp) with h7912 | h7912
                                      · linarith only [h0, h7912, hlam]
                                      · linarith only [h7494, h7912, hlam]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h7494, h7894, h7899, h7901, hc45, hlam, hphi, ht0b, ht5b, p7902_1, u0elo2]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h0, h7494, h7894, h7899, h7901, hc45, hlam, hphi, ht0b, ht5b, p7902_1, u0elo2]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [hlam, p7902_0]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h6681, h7494, h7894, h7899, h7901, hc45, hlam, hphi, ht0b, ht5b, p7902_1, u0elo2]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      rcases p7902_3 (m.d 0 1) (by simp) with h7919 | h7919
                                      · linarith only [h4610, h7919, hlam]
                                      · linarith only [h7494, h7919, hlam]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h7494, h7894, h7899, h7901, hc45, hlam, hphi, ht0b, ht5b, p7902_1, u0elo3]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h0, h7494, h7894, h7899, h7901, hc45, hlam, hphi, ht0b, ht5b, p7902_1, u0elo3]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h7840, hlam, p7902_0]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [hlam, p7902_0]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      rcases p7902_3 (m.d 0 1) (by simp) with h7926 | h7926
                                      · linarith only [h6681, h7926, hlam]
                                      · linarith only [h7494, h7926, hlam]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h7494, hlam, p7902_0]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h7839, hlam, p7902_1]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h7841, hlam, p7902_0]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [h7842, hlam, p7902_1]
                                    · have p7902_0 := h7902c.1
                                      have p7902_1 := h7902c.2.1
                                      have p7902_2 := h7902c.2.2.1
                                      have p7902_3 := h7902c.2.2.2
                                      linarith only [hlam, p7902_0]
                                  · linarith only [h0, h7494, h7892, h7897, h7898, h7901, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h7494, h7892, h7897, h7900, hlam]
                              · linarith only [h0, h7892, h7898, h7899, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h7495, h7840, h7898, hlam]
                          · linarith only [h6681, h7842, h7897, hlam]
                        · linarith only [h4610, h7841, h7896, hlam]
                      · linarith only [h4610, h7840, h7895, hlam]
                    · linarith only [h0, h7839, h7894, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h7494, h7762, h7842, hlam]
            · linarith only [h0, h7494, h7762, h7840, h7841, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7944 | h7944
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7945 | h7945
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7946 | h7946
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7947 | h7947
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7948 | h7948
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7949 | h7949
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7950 | h7950
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7951 | h7951
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7952 | h7952
                            · linarith only [h0, h7494, h7495, h7840, h7946, h7948, h7952, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h7494, h7495, h7948, h7949, h7952, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h6681, h7494, h7945, h7948, h7951, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h0, h7494, h7495, h7840, h7948, h7949, h7950, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7957 | h7957
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7958 | h7958
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7959 | h7959
                            · linarith only [h7946, h7949, h7959, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7961 | h7961
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7962 | h7962
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7963 | h7963
                                  · rcases h0bigk with h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c | h7964c
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [hlam, p7964_0]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h0, hlam, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h4610, hlam, p7964_0]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h6681, hlam, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h0, h7495, h7946, h7949, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7495, h7946, hc01, hc13, hlam, hphi, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [hlam, p7964_0]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7495, hlam, p7964_0]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7762, hlam, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7494, h7495, h7946, h7948, h7949, h7961, h7963, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7494, h7948, h7961, h7963, hc45, hlam, hphi, ht0b, ht5b, p7964_1, u0elo2]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7495, h7946, h7949, hc02, hc34, hlam, hphi, ht23, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [hlam, p7964_0]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7840, hlam, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      rcases p7964_3 (m.d 0 1) (by simp) with h7979 | h7979
                                      · linarith only [h4610, h7979, hlam]
                                      · linarith only [h7494, h7979, hlam]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7494, h7762, h7947, h7948, h7961, h7963, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h0, h7494, h7762, h7947, h7948, h7961, h7963, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h4610, h7494, h7762, h7947, h7948, h7961, h7963, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [hlam, p7964_0]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      rcases p7964_3 (m.d 0 1) (by simp) with h7986 | h7986
                                      · linarith only [h6681, h7986, hlam]
                                      · linarith only [h7494, h7986, hlam]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7494, hlam, p7964_0]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7839, hlam, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7944, hlam, p7964_0]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [h7945, hlam, p7964_1]
                                    · have p7964_0 := h7964c.1
                                      have p7964_1 := h7964c.2.1
                                      have p7964_2 := h7964c.2.2.1
                                      have p7964_3 := h7964c.2.2.2
                                      linarith only [hlam, p7964_0]
                                  · linarith only [h4610, h7949, h7963, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h0, h7494, h7495, h7762, h7946, h7949, h7958, h7962, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h7495, h7944, h7961, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h7495, h7945, h7946, h7949, h7958, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h0, h7494, h7495, h7944, h7946, h7948, h7957, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h7494, h7762, h7947, h7948, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h7494, h7495, h7946, h7947, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8001 | h8001
                  · linarith only [h0, h7494, h7762, h7946, h8001, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8003 | h8003
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8004 | h8004
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8005 | h8005
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8006 | h8006
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8007 | h8007
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8008 | h8008
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8009 | h8009
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8010 | h8010
                                  · rcases h0bigk with h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c | h8011c
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [hlam, p8011_0]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h0, hlam, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h4610, hlam, p8011_0]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h6681, hlam, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h0, h7494, h8001, h8003, h8007, h8008, h8010, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h0, h8001, h8007, hc01, hc23, hlam, hphi, ht12, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [hlam, p8011_0]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7495, hlam, p8011_0]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7762, hlam, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7494, h7495, h7840, h7946, h8003, h8004, h8008, h8010, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7494, h7840, h7946, h8003, h8004, h8008, h8010, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7840, h7946, h8004, hc02, hc23, hlam, hphi, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [hlam, p8011_0]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7840, hlam, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7494, h7840, h7946, h8003, h8004, h8008, h8010, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7494, h7840, h7946, h8003, h8004, h8008, h8010, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h0, h7494, h7840, h7946, h8003, h8004, h8008, h8010, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h4610, h7494, h7840, h7946, h8003, h8004, h8008, h8010, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [hlam, p8011_0]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      rcases p8011_3 (m.d 0 1) (by simp) with h8031 | h8031
                                      · linarith only [h6681, h8031, hlam]
                                      · linarith only [h7494, h8031, hlam]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7494, hlam, p8011_0]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7839, hlam, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7944, hlam, p8011_0]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [h7945, hlam, p8011_1]
                                    · have p8011_0 := h8011c.1
                                      have p8011_1 := h8011c.2.1
                                      have p8011_2 := h8011c.2.2.1
                                      have p8011_3 := h8011c.2.2.2
                                      linarith only [hlam, p8011_0]
                                  · linarith only [h0, h7495, h7840, h7945, h8010, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                · linarith only [h0, h7494, h8001, h8006, h8009, hlam]
                              · linarith only [h0, h7495, h7840, h7946, h8004, h8008, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h7946, h8004, h8007, hlam]
                          · linarith only [h7840, h7945, h8004, h8006, hlam]
                        · linarith only [h0, h7495, h7840, h8004, h8005, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8045 | h8045
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8046 | h8046
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8047 | h8047
                            · linarith only [h0, h7946, h8004, h8047, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h7494, h7946, h8003, h8047, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h6681, h7945, h8046, hlam]
                        · linarith only [h4610, h7944, h8045, hlam]
                    · linarith only [h0, h7839, h8003, hlam]
              · linarith only [h6681, h7494, h7945, hlam]
            · linarith only [h0, h7494, h7495, h7944, hlam]
        · linarith only [h0, h7494, h7839, hlam]
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7 m hb0 hb2 hb3 hb5 h0 h4610 h6681 h7494

end R2N4
