import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 2 3 4 (by decide) (by decide) with h25428 | h25428
  · rcases m.htr 2 3 5 (by decide) (by decide) with h25429 | h25429
    · rcases m.htr 2 4 5 (by decide) (by decide) with h25430 | h25430
      · linarith only [h22351, h22355, h25430, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h25432 | h25432
        · linarith only [h22350, h22355, h25428, h25432, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
        · rcases h0bigk with h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c | h25434c
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [hlam, p25434_0]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h0, hlam, p25434_1]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h15532, hlam, p25434_0]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h18443, hlam, p25434_1]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h20697, hlam, p25434_1]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            rcases p25434_3 (m.d 0 1) (by simp) with h25440 | h25440
            · linarith only [h0, h25440, hlam]
            · rcases p25434_3 (m.d 0 2) (by simp) with h25442 | h25442
              · rcases p25434_3 (m.d 0 3) (by simp) with h25443 | h25443
                · linarith only [h22350, h25443, hlam]
                · linarith only [h15532, h25443, hlam]
              · linarith only [h0, h25442, hlam]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [hlam, p25434_0]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            rcases p25434_3 (m.d 0 1) (by simp) with h25448 | h25448
            · linarith only [h0, h25448, hlam]
            · rcases p25434_3 (m.d 0 2) (by simp) with h25450 | h25450
              · rcases p25434_3 (m.d 0 3) (by simp) with h25451 | h25451
                · linarith only [h22350, h25451, hlam]
                · rcases p25434_3 (m.d 0 4) (by simp) with h25453 | h25453
                  · linarith only [h22351, h25453, hlam]
                  · rcases p25434_3 (m.d 0 5) (by simp) with h25455 | h25455
                    · linarith only [h22352, h25455, hlam]
                    · rcases h2bigk with h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c | h25457c
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h0, hlam, p25457_1]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        rcases p25457_3 (m.d 0 2) (by simp) with h25460 | h25460
                        · rcases p25457_3 (m.d 1 2) (by simp) with h25461 | h25461
                          · rcases p25457_3 (m.d 2 3) (by simp) with h25462 | h25462
                            · linarith only [h25462, hlam, p25457_0]
                            · rcases p25457_3 (m.d 2 4) (by simp) with h25464 | h25464
                              · linarith only [h22351, h25464, hlam]
                              · rcases p25457_3 (m.d 2 5) (by simp) with h25466 | h25466
                                · linarith only [h22352, h25466, hlam]
                                · rcases h3bigk with h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c | h25468c
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h15532, hlam, p25468_1]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25434_1, p25468_1]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25468_1]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h0, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25468_1]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    rcases p25468_3 (m.d 0 3) (by simp) with h25474 | h25474
                                    · linarith only [h15532, h25474, hlam]
                                    · rcases p25468_3 (m.d 1 3) (by simp) with h25476 | h25476
                                      · rcases p25468_3 (m.d 2 3) (by simp) with h25477 | h25477
                                        · linarith only [h25422, h25477, hlam]
                                        · rcases p25468_3 (m.d 3 4) (by simp) with h25479 | h25479
                                          · linarith only [h25425, h25479, hlam]
                                          · rcases p25468_3 (m.d 3 5) (by simp) with h25481 | h25481
                                            · linarith only [h25426, h25481, hlam]
                                            · rcases h5bigk with h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c | h25483c
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [hlam, p25483_0]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h20697, hlam, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h0, h22354, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p25434_1, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h0, h22354, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h22355, hlam, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h20697, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [hlam, p25483_0]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                rcases p25483_3 (m.d 0 5) (by simp) with h25491 | h25491
                                                · linarith only [h20697, h25491, hlam]
                                                · linarith only [h22352, h25491, hlam]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                rcases p25483_3 (m.d 0 5) (by simp) with h25494 | h25494
                                                · linarith only [h20697, h25494, hlam]
                                                · linarith only [h22354, h25494, hlam]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h18443, h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h22352, hlam, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h25424, hlam, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [hlam, p25483_0]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h0, h22352, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h25430, hlam, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h22354, hlam, p25483_0]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h25426, hlam, p25483_0]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h25429, hlam, p25483_0]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [hlam, p25483_0]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h25432, hlam, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h18443, h22355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h25427, hlam, p25483_0]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h25422, h25425, h25427, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [h25422, h25425, h25427, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25483_1]
                                              · have p25483_0 := h25483c.1
                                                have p25483_1 := h25483c.2.1
                                                have p25483_2 := h25483c.2.2.1
                                                have p25483_3 := h25483c.2.2.2
                                                linarith only [hlam, p25483_0]
                                      · linarith only [h15532, h25476, hlam]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    rcases p25468_3 (m.d 0 3) (by simp) with h25515 | h25515
                                    · linarith only [h15532, h25515, hlam]
                                    · linarith only [h22350, h25515, hlam]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    rcases p25468_3 (m.d 0 3) (by simp) with h25518 | h25518
                                    · linarith only [h15532, h25518, hlam]
                                    · linarith only [h22353, h25518, hlam]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    rcases p25468_3 (m.d 0 3) (by simp) with h25521 | h25521
                                    · linarith only [h15532, h25521, hlam]
                                    · linarith only [h22354, h25521, hlam]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h22350, hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h25422, hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h0, h22350, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25468_1]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h0, h22350, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p25434_1, p25468_1]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h22353, hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h25425, hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h25428, hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h25432, hlam, p25468_1]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h22354, hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h25426, hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h25429, hlam, p25468_0]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [h0, h22354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25468_1]
                                  · have p25468_0 := h25468c.1
                                    have p25468_1 := h25468c.2.1
                                    have p25468_2 := h25468c.2.2.1
                                    have p25468_3 := h25468c.2.2.2
                                    linarith only [hlam, p25468_0]
                          · linarith only [h25422, h25461, hlam]
                        · linarith only [h25460, hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        rcases p25457_3 (m.d 0 2) (by simp) with h25541 | h25541
                        · rcases p25457_3 (m.d 1 2) (by simp) with h25542 | h25542
                          · rcases p25457_3 (m.d 2 3) (by simp) with h25543 | h25543
                            · linarith only [h22350, h25543, hlam]
                            · linarith only [h25428, h25543, hlam]
                          · linarith only [h25423, h25542, hlam]
                        · linarith only [h25541, hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        rcases p25457_3 (m.d 0 2) (by simp) with h25548 | h25548
                        · rcases p25457_3 (m.d 1 2) (by simp) with h25549 | h25549
                          · rcases p25457_3 (m.d 2 3) (by simp) with h25550 | h25550
                            · linarith only [h22350, h25550, hlam]
                            · linarith only [h25429, h25550, hlam]
                          · linarith only [h25424, h25549, hlam]
                        · linarith only [h25548, hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25434_1, p25457_1]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        rcases p25457_3 (m.d 0 2) (by simp) with h25557 | h25557
                        · linarith only [h0, h25557, hlam]
                        · linarith only [h22350, h25557, hlam]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        rcases p25457_3 (m.d 0 2) (by simp) with h25560 | h25560
                        · linarith only [h0, h25560, hlam]
                        · linarith only [h22351, h25560, hlam]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        rcases p25457_3 (m.d 0 2) (by simp) with h25563 | h25563
                        · linarith only [h0, h25563, hlam]
                        · linarith only [h22352, h25563, hlam]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h22350, hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h25422, hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h22350, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p25434_1, p25457_1]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h0, h22350, h25428, h25430, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25457_1]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h22351, hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h25423, hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h25428, hlam, p25457_1]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h25430, hlam, p25457_1]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h22352, hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h25424, hlam, p25457_0]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h25429, hlam, p25457_1]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [h0, h22352, h22354, h25428, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25457_1]
                      · have p25457_0 := h25457c.1
                        have p25457_1 := h25457c.2.1
                        have p25457_2 := h25457c.2.2.1
                        have p25457_3 := h25457c.2.2.2
                        linarith only [hlam, p25457_0]
              · linarith only [h22350, h25450, hlam]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            rcases p25434_3 (m.d 0 1) (by simp) with h25582 | h25582
            · linarith only [h0, h25582, hlam]
            · rcases p25434_3 (m.d 0 2) (by simp) with h25584 | h25584
              · rcases p25434_3 (m.d 0 3) (by simp) with h25585 | h25585
                · linarith only [h22350, h25585, hlam]
                · linarith only [h22353, h25585, hlam]
              · linarith only [h22351, h25584, hlam]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            rcases p25434_3 (m.d 0 1) (by simp) with h25589 | h25589
            · linarith only [h0, h25589, hlam]
            · rcases p25434_3 (m.d 0 2) (by simp) with h25591 | h25591
              · rcases p25434_3 (m.d 0 3) (by simp) with h25592 | h25592
                · linarith only [h22350, h25592, hlam]
                · linarith only [h22354, h25592, hlam]
              · linarith only [h22352, h25591, hlam]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            rcases p25434_3 (m.d 0 1) (by simp) with h25596 | h25596
            · linarith only [h15532, h25596, hlam]
            · rcases p25434_3 (m.d 0 2) (by simp) with h25598 | h25598
              · rcases p25434_3 (m.d 0 3) (by simp) with h25599 | h25599
                · rcases p25434_3 (m.d 0 4) (by simp) with h25600 | h25600
                  · linarith only [h22353, h25600, hlam]
                  · linarith only [h18443, h25600, hlam]
                · linarith only [h15532, h25599, hlam]
              · linarith only [h0, h25598, hlam]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h22350, hlam, p25434_1]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [hlam, p25434_0]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            rcases p25434_3 (m.d 0 1) (by simp) with h25607 | h25607
            · linarith only [h15532, h25607, hlam]
            · rcases p25434_3 (m.d 0 2) (by simp) with h25609 | h25609
              · rcases p25434_3 (m.d 0 3) (by simp) with h25610 | h25610
                · rcases p25434_3 (m.d 0 4) (by simp) with h25611 | h25611
                  · linarith only [h22353, h25611, hlam]
                  · rcases p25434_3 (m.d 0 5) (by simp) with h25613 | h25613
                    · linarith only [h22354, h25613, hlam]
                    · linarith only [h22355, h25613, hlam]
                · linarith only [h22353, h25610, hlam]
              · linarith only [h22351, h25609, hlam]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            rcases p25434_3 (m.d 0 1) (by simp) with h25618 | h25618
            · linarith only [h15532, h25618, hlam]
            · rcases p25434_3 (m.d 0 2) (by simp) with h25620 | h25620
              · rcases p25434_3 (m.d 0 3) (by simp) with h25621 | h25621
                · rcases p25434_3 (m.d 0 4) (by simp) with h25622 | h25622
                  · linarith only [h22353, h25622, hlam]
                  · rcases p25434_3 (m.d 0 5) (by simp) with h25624 | h25624
                    · linarith only [h22354, h25624, hlam]
                    · rcases h2bigk with h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c | h25626c
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h0, hlam, p25626_1]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        rcases p25626_3 (m.d 0 2) (by simp) with h25629 | h25629
                        · rcases p25626_3 (m.d 1 2) (by simp) with h25630 | h25630
                          · rcases p25626_3 (m.d 2 3) (by simp) with h25631 | h25631
                            · linarith only [h25631, hlam, p25626_0]
                            · rcases p25626_3 (m.d 2 4) (by simp) with h25633 | h25633
                              · linarith only [h22351, h25633, hlam]
                              · rcases p25626_3 (m.d 2 5) (by simp) with h25635 | h25635
                                · linarith only [h22352, h25635, hlam]
                                · rcases h3bigk with h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c | h25637c
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h15532, hlam, p25637_1]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    rcases p25637_3 (m.d 0 3) (by simp) with h25640 | h25640
                                    · rcases p25637_3 (m.d 1 3) (by simp) with h25641 | h25641
                                      · rcases p25637_3 (m.d 2 3) (by simp) with h25642 | h25642
                                        · linarith only [h22350, h25642, hlam]
                                        · rcases p25637_3 (m.d 3 4) (by simp) with h25644 | h25644
                                          · linarith only [h22353, h25644, hlam]
                                          · rcases p25637_3 (m.d 3 5) (by simp) with h25646 | h25646
                                            · linarith only [h22354, h25646, hlam]
                                            · rcases h5bigk with h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c | h25648c
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [hlam, p25648_0]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h20697, hlam, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h0, h22350, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p25434_1, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h0, h22350, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h22355, hlam, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h20697, h25427, hc01, hc14, hlam, hphi, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [hlam, p25648_0]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                rcases p25648_3 (m.d 0 5) (by simp) with h25656 | h25656
                                                · linarith only [h20697, h25656, hlam]
                                                · linarith only [h22352, h25656, hlam]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                rcases p25648_3 (m.d 0 5) (by simp) with h25659 | h25659
                                                · linarith only [h20697, h25659, hlam]
                                                · linarith only [h22354, h25659, hlam]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h18443, h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h22352, hlam, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h25424, hlam, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [hlam, p25648_0]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h0, h22352, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h25430, hlam, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h22354, hlam, p25648_0]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h25426, hlam, p25648_0]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h25429, hlam, p25648_0]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [hlam, p25648_0]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h25432, hlam, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h20697, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h25427, hlam, p25648_0]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h25422, h25425, h25427, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [h25422, h25425, h25427, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25648_1]
                                              · have p25648_0 := h25648c.1
                                                have p25648_1 := h25648c.2.1
                                                have p25648_2 := h25648c.2.2.1
                                                have p25648_3 := h25648c.2.2.2
                                                linarith only [hlam, p25648_0]
                                      · linarith only [h25422, h25641, hlam]
                                    · linarith only [h22350, h25640, hlam]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    rcases p25637_3 (m.d 0 3) (by simp) with h25680 | h25680
                                    · rcases p25637_3 (m.d 1 3) (by simp) with h25681 | h25681
                                      · rcases p25637_3 (m.d 2 3) (by simp) with h25682 | h25682
                                        · linarith only [h22350, h25682, hlam]
                                        · linarith only [h25428, h25682, hlam]
                                      · linarith only [h25425, h25681, hlam]
                                    · linarith only [h25680, hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    rcases p25637_3 (m.d 0 3) (by simp) with h25687 | h25687
                                    · rcases p25637_3 (m.d 1 3) (by simp) with h25688 | h25688
                                      · rcases p25637_3 (m.d 2 3) (by simp) with h25689 | h25689
                                        · linarith only [h22350, h25689, hlam]
                                        · linarith only [h25429, h25689, hlam]
                                      · linarith only [h25426, h25688, hlam]
                                    · linarith only [h25687, hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h18443, h22355, h25422, hc01, hc12, hlam, hphi, p25434_1, p25637_1]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    rcases p25637_3 (m.d 0 3) (by simp) with h25696 | h25696
                                    · linarith only [h15532, h25696, hlam]
                                    · linarith only [h22350, h25696, hlam]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    rcases p25637_3 (m.d 0 3) (by simp) with h25699 | h25699
                                    · linarith only [h15532, h25699, hlam]
                                    · linarith only [h22353, h25699, hlam]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    rcases p25637_3 (m.d 0 3) (by simp) with h25702 | h25702
                                    · linarith only [h15532, h25702, hlam]
                                    · linarith only [h22354, h25702, hlam]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h22350, hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h25422, hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25626_1, p25637_1]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h0, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25626_1, p25637_1]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h22353, hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h25425, hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h25428, hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h25432, hlam, p25637_1]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h22354, hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h25426, hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h25429, hlam, p25637_0]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [h22352, h25429, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p25434_1, p25637_1]
                                  · have p25637_0 := h25637c.1
                                    have p25637_1 := h25637c.2.1
                                    have p25637_2 := h25637c.2.2.1
                                    have p25637_3 := h25637c.2.2.2
                                    linarith only [hlam, p25637_0]
                          · linarith only [h25422, h25630, hlam]
                        · linarith only [h25629, hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        rcases p25626_3 (m.d 0 2) (by simp) with h25722 | h25722
                        · rcases p25626_3 (m.d 1 2) (by simp) with h25723 | h25723
                          · rcases p25626_3 (m.d 2 3) (by simp) with h25724 | h25724
                            · linarith only [h22350, h25724, hlam]
                            · linarith only [h25428, h25724, hlam]
                          · linarith only [h25423, h25723, hlam]
                        · linarith only [h25722, hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        rcases p25626_3 (m.d 0 2) (by simp) with h25729 | h25729
                        · rcases p25626_3 (m.d 1 2) (by simp) with h25730 | h25730
                          · rcases p25626_3 (m.d 2 3) (by simp) with h25731 | h25731
                            · linarith only [h22350, h25731, hlam]
                            · linarith only [h25429, h25731, hlam]
                          · linarith only [h25424, h25730, hlam]
                        · linarith only [h25729, hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h22350, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p25434_1, p25626_1]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        rcases p25626_3 (m.d 0 2) (by simp) with h25738 | h25738
                        · linarith only [h0, h25738, hlam]
                        · linarith only [h22350, h25738, hlam]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        rcases p25626_3 (m.d 0 2) (by simp) with h25741 | h25741
                        · linarith only [h0, h25741, hlam]
                        · linarith only [h22351, h25741, hlam]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        rcases p25626_3 (m.d 0 2) (by simp) with h25744 | h25744
                        · linarith only [h0, h25744, hlam]
                        · linarith only [h22352, h25744, hlam]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h22350, hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h25422, hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        rcases p25626_3 (m.d 0 2) (by simp) with h25750 | h25750
                        · rcases p25626_3 (m.d 1 2) (by simp) with h25751 | h25751
                          · rcases p25626_3 (m.d 2 3) (by simp) with h25752 | h25752
                            · rcases p25626_3 (m.d 2 4) (by simp) with h25753 | h25753
                              · linarith only [h25428, h25753, hlam]
                              · rcases p25626_3 (m.d 2 5) (by simp) with h25755 | h25755
                                · linarith only [h25429, h25755, hlam]
                                · linarith only [h25430, h25755, hlam]
                            · linarith only [h25428, h25752, hlam]
                          · linarith only [h25423, h25751, hlam]
                        · linarith only [h22351, h25750, hlam]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        rcases p25626_3 (m.d 0 2) (by simp) with h25761 | h25761
                        · rcases p25626_3 (m.d 1 2) (by simp) with h25762 | h25762
                          · rcases p25626_3 (m.d 2 3) (by simp) with h25763 | h25763
                            · rcases p25626_3 (m.d 2 4) (by simp) with h25764 | h25764
                              · linarith only [h25428, h25764, hlam]
                              · rcases p25626_3 (m.d 2 5) (by simp) with h25766 | h25766
                                · linarith only [h25429, h25766, hlam]
                                · rcases h3bigk with h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c | h25768c
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h15532, hlam, p25768_1]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h25430, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p25626_1, p25768_1]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    rcases p25768_3 (m.d 0 3) (by simp) with h25772 | h25772
                                    · rcases p25768_3 (m.d 1 3) (by simp) with h25773 | h25773
                                      · rcases p25768_3 (m.d 2 3) (by simp) with h25774 | h25774
                                        · linarith only [h22350, h25774, hlam]
                                        · linarith only [h25428, h25774, hlam]
                                      · linarith only [h25425, h25773, hlam]
                                    · linarith only [h25772, hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    rcases p25768_3 (m.d 0 3) (by simp) with h25779 | h25779
                                    · rcases p25768_3 (m.d 1 3) (by simp) with h25780 | h25780
                                      · rcases p25768_3 (m.d 2 3) (by simp) with h25781 | h25781
                                        · linarith only [h22350, h25781, hlam]
                                        · linarith only [h25429, h25781, hlam]
                                      · linarith only [h25426, h25780, hlam]
                                    · linarith only [h25779, hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h22350, h25422, h25428, h25430, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25626_1, p25768_1]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h25422, h25428, h25430, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25626_1, p25768_1]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    rcases p25768_3 (m.d 0 3) (by simp) with h25789 | h25789
                                    · linarith only [h15532, h25789, hlam]
                                    · linarith only [h22353, h25789, hlam]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    rcases p25768_3 (m.d 0 3) (by simp) with h25792 | h25792
                                    · linarith only [h15532, h25792, hlam]
                                    · linarith only [h22354, h25792, hlam]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h22350, hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h25422, hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    rcases p25768_3 (m.d 0 3) (by simp) with h25798 | h25798
                                    · rcases p25768_3 (m.d 1 3) (by simp) with h25799 | h25799
                                      · rcases p25768_3 (m.d 2 3) (by simp) with h25800 | h25800
                                        · rcases p25768_3 (m.d 3 4) (by simp) with h25801 | h25801
                                          · linarith only [h25801, hlam, p25768_0]
                                          · rcases p25768_3 (m.d 3 5) (by simp) with h25803 | h25803
                                            · linarith only [h25429, h25803, hlam]
                                            · linarith only [h25432, h25803, hlam]
                                        · linarith only [h25800, hlam, p25768_0]
                                      · linarith only [h25425, h25799, hlam]
                                    · linarith only [h22353, h25798, hlam]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    rcases p25768_3 (m.d 0 3) (by simp) with h25809 | h25809
                                    · rcases p25768_3 (m.d 1 3) (by simp) with h25810 | h25810
                                      · rcases p25768_3 (m.d 2 3) (by simp) with h25811 | h25811
                                        · rcases p25768_3 (m.d 3 4) (by simp) with h25812 | h25812
                                          · linarith only [h25428, h25812, hlam]
                                          · rcases p25768_3 (m.d 3 5) (by simp) with h25814 | h25814
                                            · linarith only [h25814, hlam, p25768_0]
                                            · rcases h5bigk with h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c | h25816c
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [hlam, p25816_0]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h20697, hlam, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h25428, h25430, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p25434_1, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h0, h22350, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h22355, hlam, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h18443, h22355, h25425, h25427, hc01, hc13, hlam, hphi, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [hlam, p25816_0]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                rcases p25816_3 (m.d 0 5) (by simp) with h25824 | h25824
                                                · linarith only [h20697, h25824, hlam]
                                                · linarith only [h22352, h25824, hlam]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                rcases p25816_3 (m.d 0 5) (by simp) with h25827 | h25827
                                                · linarith only [h20697, h25827, hlam]
                                                · linarith only [h22354, h25827, hlam]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h18443, h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h22352, hlam, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h25424, hlam, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [hlam, p25816_0]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h25432, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p25626_1, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h25430, hlam, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h22354, hlam, p25816_0]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h25426, hlam, p25816_0]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h25429, hlam, p25816_0]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [hlam, p25816_0]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h25432, hlam, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h18443, h22355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h25427, hlam, p25816_0]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h25422, h25425, h25427, h25429, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [h25422, h25425, h25427, h25432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25816_1]
                                              · have p25816_0 := h25816c.1
                                                have p25816_1 := h25816c.2.1
                                                have p25816_2 := h25816c.2.2.1
                                                have p25816_3 := h25816c.2.2.2
                                                linarith only [hlam, p25816_0]
                                        · linarith only [h25811, hlam, p25768_0]
                                      · linarith only [h25426, h25810, hlam]
                                    · linarith only [h22354, h25809, hlam]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h22353, hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h25425, hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h25428, hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h25432, hlam, p25768_1]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h22354, hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h25426, hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h25429, hlam, p25768_0]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [h0, h22350, h22352, h25429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25768_1]
                                  · have p25768_0 := h25768c.1
                                    have p25768_1 := h25768c.2.1
                                    have p25768_2 := h25768c.2.2.1
                                    have p25768_3 := h25768c.2.2.2
                                    linarith only [hlam, p25768_0]
                            · linarith only [h25429, h25763, hlam]
                          · linarith only [h25424, h25762, hlam]
                        · linarith only [h22352, h25761, hlam]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h22351, hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h25423, hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h25428, hlam, p25626_1]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h25430, hlam, p25626_1]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h22352, hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h25424, hlam, p25626_0]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h25429, hlam, p25626_1]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [h0, h22350, h22352, h25428, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25434_1, p25626_1]
                      · have p25626_0 := h25626c.1
                        have p25626_1 := h25626c.2.1
                        have p25626_2 := h25626c.2.2.1
                        have p25626_3 := h25626c.2.2.2
                        linarith only [hlam, p25626_0]
                · linarith only [h22354, h25621, hlam]
              · linarith only [h22352, h25620, hlam]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25434_1]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h22351, hlam, p25434_0]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h22353, hlam, p25434_0]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [hlam, p25434_0]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h22355, hlam, p25434_0]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25434_1]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h22352, hlam, p25434_1]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h22354, hlam, p25434_0]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [h18443, h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25434_1]
          · have p25434_0 := h25434c.1
            have p25434_1 := h25434c.2.1
            have p25434_2 := h25434c.2.2.1
            have p25434_3 := h25434c.2.2.2
            linarith only [hlam, p25434_0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h25884 | h25884
      · linarith only [h22351, h22355, h25884, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h25886 | h25886
        · linarith only [h22354, h22355, h25428, h25429, h25886, hlam]
        · rcases h0bigk with h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c | h25888c
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [hlam, p25888_0]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h0, hlam, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h15532, hlam, p25888_0]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h18443, hlam, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h20697, hlam, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            rcases p25888_3 (m.d 0 1) (by simp) with h25894 | h25894
            · linarith only [h0, h25894, hlam]
            · rcases p25888_3 (m.d 0 2) (by simp) with h25896 | h25896
              · rcases p25888_3 (m.d 0 3) (by simp) with h25897 | h25897
                · linarith only [h22350, h25897, hlam]
                · linarith only [h15532, h25897, hlam]
              · linarith only [h0, h25896, hlam]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [hlam, p25888_0]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h0, h22354, h25428, h25429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            rcases p25888_3 (m.d 0 1) (by simp) with h25903 | h25903
            · linarith only [h0, h25903, hlam]
            · rcases p25888_3 (m.d 0 2) (by simp) with h25905 | h25905
              · rcases p25888_3 (m.d 0 3) (by simp) with h25906 | h25906
                · linarith only [h22350, h25906, hlam]
                · linarith only [h22353, h25906, hlam]
              · linarith only [h22351, h25905, hlam]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h0, h22354, h25428, h25429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            rcases p25888_3 (m.d 0 1) (by simp) with h25911 | h25911
            · linarith only [h15532, h25911, hlam]
            · rcases p25888_3 (m.d 0 2) (by simp) with h25913 | h25913
              · rcases p25888_3 (m.d 0 3) (by simp) with h25914 | h25914
                · rcases p25888_3 (m.d 0 4) (by simp) with h25915 | h25915
                  · linarith only [h22353, h25915, hlam]
                  · linarith only [h18443, h25915, hlam]
                · linarith only [h15532, h25914, hlam]
              · linarith only [h0, h25913, hlam]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h22350, hlam, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [hlam, p25888_0]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            rcases p25888_3 (m.d 0 1) (by simp) with h25922 | h25922
            · linarith only [h15532, h25922, hlam]
            · rcases p25888_3 (m.d 0 2) (by simp) with h25924 | h25924
              · rcases p25888_3 (m.d 0 3) (by simp) with h25925 | h25925
                · rcases p25888_3 (m.d 0 4) (by simp) with h25926 | h25926
                  · linarith only [h22353, h25926, hlam]
                  · rcases p25888_3 (m.d 0 5) (by simp) with h25928 | h25928
                    · linarith only [h22354, h25928, hlam]
                    · linarith only [h22355, h25928, hlam]
                · linarith only [h22353, h25925, hlam]
              · linarith only [h22351, h25924, hlam]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h22354, h25428, h25429, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h22351, hlam, p25888_0]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h22353, hlam, p25888_0]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [hlam, p25888_0]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h22355, hlam, p25888_0]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h22352, hlam, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h22354, hlam, p25888_0]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [h18443, h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25888_1]
          · have p25888_0 := h25888c.1
            have p25888_1 := h25888c.2.1
            have p25888_2 := h25888c.2.2.1
            have p25888_3 := h25888c.2.2.2
            linarith only [hlam, p25888_0]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h25944 | h25944
    · linarith only [h22353, h22355, h25422, h25425, h25427, h25428, h25944, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h25946 | h25946
      · linarith only [h22353, h22355, h25428, h25946, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h25948 | h25948
        · linarith only [h22353, h22355, h25948, hlam]
        · rcases h0bigk with h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c | h25950c
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [hlam, p25950_0]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h0, hlam, p25950_1]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h15532, hlam, p25950_0]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h18443, hlam, p25950_1]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h20697, hlam, p25950_1]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            rcases p25950_3 (m.d 0 1) (by simp) with h25956 | h25956
            · linarith only [h0, h25956, hlam]
            · rcases p25950_3 (m.d 0 2) (by simp) with h25958 | h25958
              · rcases p25950_3 (m.d 0 3) (by simp) with h25959 | h25959
                · linarith only [h22350, h25959, hlam]
                · linarith only [h15532, h25959, hlam]
              · linarith only [h0, h25958, hlam]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [hlam, p25950_0]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h0, h22353, h25428, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25950_1]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            rcases p25950_3 (m.d 0 1) (by simp) with h25965 | h25965
            · linarith only [h0, h25965, hlam]
            · rcases p25950_3 (m.d 0 2) (by simp) with h25967 | h25967
              · rcases p25950_3 (m.d 0 3) (by simp) with h25968 | h25968
                · linarith only [h22350, h25968, hlam]
                · linarith only [h22353, h25968, hlam]
              · linarith only [h22351, h25967, hlam]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            rcases p25950_3 (m.d 0 1) (by simp) with h25972 | h25972
            · linarith only [h0, h25972, hlam]
            · rcases p25950_3 (m.d 0 2) (by simp) with h25974 | h25974
              · rcases p25950_3 (m.d 0 3) (by simp) with h25975 | h25975
                · linarith only [h22350, h25975, hlam]
                · linarith only [h22354, h25975, hlam]
              · linarith only [h22352, h25974, hlam]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            rcases p25950_3 (m.d 0 1) (by simp) with h25979 | h25979
            · linarith only [h15532, h25979, hlam]
            · rcases p25950_3 (m.d 0 2) (by simp) with h25981 | h25981
              · rcases p25950_3 (m.d 0 3) (by simp) with h25982 | h25982
                · rcases p25950_3 (m.d 0 4) (by simp) with h25983 | h25983
                  · linarith only [h22353, h25983, hlam]
                  · linarith only [h18443, h25983, hlam]
                · linarith only [h15532, h25982, hlam]
              · linarith only [h0, h25981, hlam]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h22350, hlam, p25950_1]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [hlam, p25950_0]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            rcases p25950_3 (m.d 0 1) (by simp) with h25990 | h25990
            · linarith only [h15532, h25990, hlam]
            · rcases p25950_3 (m.d 0 2) (by simp) with h25992 | h25992
              · rcases p25950_3 (m.d 0 3) (by simp) with h25993 | h25993
                · rcases p25950_3 (m.d 0 4) (by simp) with h25994 | h25994
                  · linarith only [h22353, h25994, hlam]
                  · rcases p25950_3 (m.d 0 5) (by simp) with h25996 | h25996
                    · linarith only [h22354, h25996, hlam]
                    · linarith only [h22355, h25996, hlam]
                · linarith only [h22353, h25993, hlam]
              · linarith only [h22351, h25992, hlam]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            rcases p25950_3 (m.d 0 1) (by simp) with h26001 | h26001
            · linarith only [h15532, h26001, hlam]
            · rcases p25950_3 (m.d 0 2) (by simp) with h26003 | h26003
              · rcases p25950_3 (m.d 0 3) (by simp) with h26004 | h26004
                · rcases p25950_3 (m.d 0 4) (by simp) with h26005 | h26005
                  · linarith only [h22353, h26005, hlam]
                  · rcases p25950_3 (m.d 0 5) (by simp) with h26007 | h26007
                    · linarith only [h22354, h26007, hlam]
                    · rcases h2bigk with h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c | h26009c
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h0, hlam, p26009_1]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h22350, h22353, h22355, h25428, hlam, p25950_1, p26009_2]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        rcases p26009_3 (m.d 0 2) (by simp) with h26013 | h26013
                        · rcases p26009_3 (m.d 1 2) (by simp) with h26014 | h26014
                          · rcases p26009_3 (m.d 2 3) (by simp) with h26015 | h26015
                            · linarith only [h22350, h26015, hlam]
                            · rcases p26009_3 (m.d 2 4) (by simp) with h26017 | h26017
                              · linarith only [h26017, hlam, p26009_0]
                              · rcases p26009_3 (m.d 2 5) (by simp) with h26019 | h26019
                                · linarith only [h22352, h26019, hlam]
                                · linarith only [h25946, h26019, hlam]
                          · linarith only [h25423, h26014, hlam]
                        · linarith only [h26013, hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        rcases p26009_3 (m.d 0 2) (by simp) with h26024 | h26024
                        · rcases p26009_3 (m.d 1 2) (by simp) with h26025 | h26025
                          · rcases p26009_3 (m.d 2 3) (by simp) with h26026 | h26026
                            · linarith only [h22350, h26026, hlam]
                            · rcases p26009_3 (m.d 2 4) (by simp) with h26028 | h26028
                              · linarith only [h22351, h26028, hlam]
                              · rcases p26009_3 (m.d 2 5) (by simp) with h26030 | h26030
                                · linarith only [h26030, hlam, p26009_0]
                                · rcases h3bigk with h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h15532, hlam, p26032_1]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h22353, h22355, h25428, hlam, p25950_1, p26032_2]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    rcases p26032_3 (m.d 0 3) (by simp) with h26036 | h26036
                                    · rcases p26032_3 (m.d 1 3) (by simp) with h26037 | h26037
                                      · rcases p26032_3 (m.d 2 3) (by simp) with h26038 | h26038
                                        · linarith only [h22350, h26038, hlam]
                                        · rcases p26032_3 (m.d 3 4) (by simp) with h26040 | h26040
                                          · linarith only [h26040, hlam, p26032_0]
                                          · rcases p26032_3 (m.d 3 5) (by simp) with h26042 | h26042
                                            · linarith only [h22354, h26042, hlam]
                                            · linarith only [h25948, h26042, hlam]
                                      · linarith only [h25425, h26037, hlam]
                                    · linarith only [h26036, hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    rcases p26032_3 (m.d 0 3) (by simp) with h26047 | h26047
                                    · rcases p26032_3 (m.d 1 3) (by simp) with h26048 | h26048
                                      · rcases p26032_3 (m.d 2 3) (by simp) with h26049 | h26049
                                        · linarith only [h22350, h26049, hlam]
                                        · rcases p26032_3 (m.d 3 4) (by simp) with h26051 | h26051
                                          · linarith only [h22353, h26051, hlam]
                                          · rcases p26032_3 (m.d 3 5) (by simp) with h26053 | h26053
                                            · linarith only [h26053, hlam, p26032_0]
                                            · rcases h5bigk with h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c | h26055c
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [hlam, p26055_0]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h20697, hlam, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h22350, hc02, hc25, hlam, hphi, ht0b, ht5b, p25950_1, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h22350, hc02, hc35, hlam, hphi, ht0b, ht5b, p25950_1, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h22355, hlam, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h20697, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [hlam, p26055_0]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                rcases p26055_3 (m.d 0 5) (by simp) with h26063 | h26063
                                                · linarith only [h20697, h26063, hlam]
                                                · linarith only [h22352, h26063, hlam]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h25422, h25425, h25427, h25428, h25948, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h22353, h22355, h25422, h25425, h25427, h25428, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h22352, hlam, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h25424, hlam, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [hlam, p26055_0]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h25944, hlam, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h25946, hlam, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h22354, hlam, p26055_0]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h25426, hlam, p26055_0]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h22350, h22353, h22355, h25428, hc23, hc35, hlam, hphi, p25950_1, p26009_2, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [hlam, p26055_0]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h25948, hlam, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h22353, h22355, h25428, hc23, hc45, hlam, hphi, ht34, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h25427, hlam, p26055_0]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h22350, h22353, h22355, h25422, h25425, h25427, h25428, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25950_1, p26009_2, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [h25422, h25425, h25427, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p26055_1]
                                              · have p26055_0 := h26055c.1
                                                have p26055_1 := h26055c.2.1
                                                have p26055_2 := h26055c.2.2.1
                                                have p26055_3 := h26055c.2.2.2
                                                linarith only [hlam, p26055_0]
                                      · linarith only [h25426, h26048, hlam]
                                    · linarith only [h26047, hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h22353, h22355, h25422, h25428, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25950_1, p26032_1]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h15532, h22353, h22355, h25428, hlam, p25950_1, p26032_2]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    rcases p26032_3 (m.d 0 3) (by simp) with h26088 | h26088
                                    · linarith only [h15532, h26088, hlam]
                                    · linarith only [h22353, h26088, hlam]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    rcases p26032_3 (m.d 0 3) (by simp) with h26091 | h26091
                                    · linarith only [h15532, h26091, hlam]
                                    · linarith only [h22354, h26091, hlam]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h22350, hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h25422, hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h25428, hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h25944, hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h22353, hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h25425, hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h22350, h22353, h22355, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25950_1, p26032_1]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h25948, hlam, p26032_1]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h22354, hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h25426, hlam, p26032_0]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h0, h22350, h22354, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25950_1, p26032_1]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [h0, h22350, h22354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25950_1, p26032_1]
                                  · have p26032_0 := h26032c.1
                                    have p26032_1 := h26032c.2.1
                                    have p26032_2 := h26032c.2.2.1
                                    have p26032_3 := h26032c.2.2.2
                                    linarith only [hlam, p26032_0]
                          · linarith only [h25424, h26025, hlam]
                        · linarith only [h26024, hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h22350, h22355, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p25950_1, p26009_1]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h0, h22350, h22353, h22355, h25428, hlam, p25950_1, p26009_2]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        rcases p26009_3 (m.d 0 2) (by simp) with h26114 | h26114
                        · linarith only [h0, h26114, hlam]
                        · linarith only [h22351, h26114, hlam]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        rcases p26009_3 (m.d 0 2) (by simp) with h26117 | h26117
                        · linarith only [h0, h26117, hlam]
                        · linarith only [h22352, h26117, hlam]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h22350, hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h25422, hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h25428, hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h25944, hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h22351, hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h25423, hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h0, h22350, h22351, h22355, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25950_1, p26009_1]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h25946, hlam, p26009_1]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h22352, hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h25424, hlam, p26009_0]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h0, h22350, h22352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25950_1, p26009_1]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [h0, h22350, h22354, h25944, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p25950_1, p26009_1]
                      · have p26009_0 := h26009c.1
                        have p26009_1 := h26009c.2.1
                        have p26009_2 := h26009c.2.2.1
                        have p26009_3 := h26009c.2.2.2
                        linarith only [hlam, p26009_0]
                · linarith only [h22354, h26004, hlam]
              · linarith only [h22352, h26003, hlam]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25950_1]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h22351, hlam, p25950_0]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h22353, hlam, p25950_0]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [hlam, p25950_0]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h22355, hlam, p25950_0]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25950_1]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h22352, hlam, p25950_1]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h22354, hlam, p25950_0]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [h18443, h22355, h25422, h25425, h25427, hc01, hc12, hlam, hphi, p25950_1]
          · have p25950_0 := h25950c.1
            have p25950_1 := h25950c.2.1
            have p25950_2 := h25950c.2.2.1
            have p25950_3 := h25950c.2.2.2
            linarith only [hlam, p25950_0]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  linarith only [h18443, h25427, h26149, hc01, hc24, hlam, hphi, ht12]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  linarith only [h18443, h25427, h26147, h26151, hc01, hc24, hlam, hphi, ht12]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  linarith only [hlam, p26153_0]

end R2N4
