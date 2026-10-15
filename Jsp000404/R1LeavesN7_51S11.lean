import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_51S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h423 | h423
  · rcases m.htr 0 3 4 (by decide) (by decide) with h424 | h424
    · rcases m.htr 0 4 5 (by decide) (by decide) with h425 | h425
      · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
        · linarith only [h0, h4, h423, h426, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h428 | h428
          · rcases m.htr 1 3 4 (by decide) (by decide) with h429 | h429
            · rcases m.htr 1 3 5 (by decide) (by decide) with h430 | h430
              · rcases m.htr 1 4 5 (by decide) (by decide) with h431 | h431
                · rcases m.htr 2 3 4 (by decide) (by decide) with h432 | h432
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h433 | h433
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h434 | h434
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h435 | h435
                        · rcases h4bigk with h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [hlam, p436_0]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h428, h433, h434, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p436_1, u3ehi4]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h4, h423, h433, h434, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p436_1, u3ehi4]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h4, h423, h435, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p436_1, u3ehi4]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h4, h423, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p436_1]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h2, hlam, p436_1]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [hlam, p436_0]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h433, h434, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p436_1, u3ehi4]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h428, h435, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p436_1, u3ehi4]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h0, h4, h428, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p436_1]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h423, hlam, p436_1]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h428, hlam, p436_1]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [hlam, p436_0]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h435, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p436_1, u3ehi4]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h0, h4, h428, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p436_1]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h424, hlam, p436_1]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h429, hlam, p436_0]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h432, hlam, p436_0]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [hlam, p436_0]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h424, hc03, hc45, hlam, hphi, ht0b, ht5b, p436_1]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h425, hlam, p436_0]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h431, hlam, p436_0]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h434, hlam, p436_0]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [h435, hlam, p436_0]
                          · have p436_0 := h436c.1
                            have p436_1 := h436c.2.1
                            have p436_2 := h436c.2.2.1
                            have p436_3 := h436c.2.2.2
                            linarith only [hlam, p436_0]
                        · linarith only [h4, h423, h425, h435, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h4, h428, h431, h432, h434, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h4, h423, h432, h433, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h3, h4, h423, h425, h429, h430, h432, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h4, h423, h425, h429, h431, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h429, h430, hc35, hlam, hphi, u3ehi3]
            · linarith only [h426, h428, h429, hlam]
          · linarith only [h4, h423, h428, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h470 | h470
        · linarith only [h0, h4, h423, h470, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h472 | h472
          · rcases m.htr 1 3 4 (by decide) (by decide) with h473 | h473
            · rcases m.htr 1 3 5 (by decide) (by decide) with h474 | h474
              · rcases m.htr 1 4 5 (by decide) (by decide) with h475 | h475
                · linarith only [h2, h425, h475, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h478 | h478
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h479 | h479
                      · linarith only [h2, h425, h472, h479, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h481 | h481
                        · linarith only [h2, h425, h472, h477, h481, hlam]
                        · rcases h4bigk with h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [hlam, p483_0]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h472, h477, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p483_1, u3ehi3]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h425, h477, hc45, hlam, hphi, ht34, p483_1, u3ehi3]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h425, hc45, hlam, hphi, ht34, p483_1, u3ehi3]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h425, hlam, p483_0]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h2, hlam, p483_1]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [hlam, p483_0]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h477, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p483_1, u3ehi3]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h2, h425, hc45, hlam, hphi, ht34, p483_1, u3ehi3]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h475, hlam, p483_0]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h423, hlam, p483_1]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h472, hlam, p483_1]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [hlam, p483_0]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h472, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p483_1, u3ehi3]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h479, hlam, p483_0]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h424, hlam, p483_1]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h473, hlam, p483_0]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h477, hlam, p483_0]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [hlam, p483_0]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h481, hlam, p483_0]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [hc04, hc45, hlam, hphi, p483_1]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h473, hc45, hlam, hphi, ht34, p483_1, u3ehi3]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [h477, hc45, hlam, hphi, ht34, p483_1, u3ehi3]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p483_1, u3ehi3]
                          · have p483_0 := h483c.1
                            have p483_1 := h483c.2.1
                            have p483_2 := h483c.2.2.1
                            have p483_3 := h483c.2.2.2
                            linarith only [hlam, p483_0]
                    · linarith only [h1, h4, h474, h478, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1, h4, h474, h477, hc34, hlam, hphi, u3ehi4]
              · linarith only [h473, h474, hc35, hlam, hphi, u3ehi3]
            · linarith only [h424, h425, h473, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h4, h423, h472, hc12, hc23, hlam, hphi]
    · linarith only [h4, h423, h424, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h515 | h515
    · rcases m.htr 0 4 5 (by decide) (by decide) with h516 | h516
      · rcases m.htr 1 2 3 (by decide) (by decide) with h517 | h517
        · linarith only [h0, h4, h517, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h519 | h519
          · linarith only [h0, h423, h519, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h521 | h521
            · rcases m.htr 1 3 5 (by decide) (by decide) with h522 | h522
              · rcases m.htr 1 4 5 (by decide) (by decide) with h523 | h523
                · rcases m.htr 2 3 4 (by decide) (by decide) with h524 | h524
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h525 | h525
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h526 | h526
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h527 | h527
                        · rcases h4bigk with h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h4, h515, h519, hc12, hc23, hlam, hphi, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h423, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h4, h515, h527, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p528_1, u3ehi4]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            rcases p528_3 (m.d 0 4) (by simp) with h533 | h533
                            · rcases p528_3 (m.d 1 4) (by simp) with h534 | h534
                              · linarith only [h2, h534, hlam]
                              · linarith only [h523, h534, hlam]
                            · linarith only [h533, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h2, hlam, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h519, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h527, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p528_1, u3ehi4]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h1, h521, hc01, hc45, hlam, hphi, ht0b, ht5b, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h0, h423, hc12, hc24, hlam, hphi, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h519, hc12, hc24, hlam, hphi, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h524, h527, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p528_1, u3ehi4]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            rcases p528_3 (m.d 0 4) (by simp) with h547 | h547
                            · linarith only [h423, h547, hlam]
                            · linarith only [h516, h547, hlam]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h515, hlam, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h521, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h524, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h2, h521, hc01, hc45, hlam, hphi, ht0b, ht5b, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h516, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h523, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h526, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h527, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hlam, p528_0]
                        · linarith only [h1, h521, h523, h527, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2, h423, h523, h526, hlam]
                    · linarith only [h4, h515, h525, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h4, h521, h524, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h564 | h564
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h565 | h565
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h566 | h566
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h567 | h567
                        · linarith only [h521, h523, h567, hlam]
                        · rcases h4bigk with h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h515, h521, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p569_1, u3ehi3]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h423, hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h4, h515, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p569_1, u3ehi3]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h4, h515, h521, h523, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p569_1, u3ehi3]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h2, hlam, p569_1]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h519, hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p569_1, u3ehi3]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h523, hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h423, h564, hc02, hc23, hlam, hphi, p569_1]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h519, h564, hc12, hc23, hlam, hphi, p569_1]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h564, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p569_1, u3ehi3]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h521, h523, h564, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p569_1, u3ehi3]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h515, hlam, p569_1]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h521, hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h564, hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h567, hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h516, hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h516, h521, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p569_1, u3ehi3]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h566, hlam, p569_0]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [h423, h516, h564, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p569_1, u3ehi3]
                          · have p569_0 := h569c.1
                            have p569_1 := h569c.2.1
                            have p569_2 := h569c.2.2.1
                            have p569_3 := h569c.2.2.2
                            linarith only [hlam, p569_0]
                      · linarith only [h423, h516, h566, hlam]
                    · linarith only [h1, h4, h522, h565, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h4, h515, h516, h521, h523, h564, hlam]
              · linarith only [h521, h522, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h599 | h599
              · linarith only [h4, h515, h521, h599, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h601 | h601
                · rcases m.htr 2 3 4 (by decide) (by decide) with h602 | h602
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h603 | h603
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h604 | h604
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h605 | h605
                        · rcases h4bigk with h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h601, hc04, hc45, hlam, hphi, ht0b, ht5b, p606_1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h423, hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h4, h515, h599, h605, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p606_1, u3ehi1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            rcases p606_3 (m.d 0 4) (by simp) with h611 | h611
                            · rcases p606_3 (m.d 1 4) (by simp) with h612 | h612
                              · linarith only [h2, h612, hlam]
                              · linarith only [h601, h612, hlam]
                            · linarith only [h611, hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h2, hlam, p606_1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h519, hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h521, hlam, p606_1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p606_1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h0, h423, h602, hc12, hc23, hlam, hphi, p606_1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h519, h602, hc12, hc23, hlam, hphi, p606_1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h599, h602, h605, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p606_1, u3ehi1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            rcases p606_3 (m.d 0 4) (by simp) with h625 | h625
                            · linarith only [h423, h625, hlam]
                            · linarith only [h516, h625, hlam]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h515, hlam, p606_1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h4, h515, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p606_1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h602, hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h4, h515, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p606_1]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h516, hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h601, hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h604, hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [h605, hlam, p606_0]
                          · have p606_0 := h606c.1
                            have p606_1 := h606c.2.1
                            have p606_2 := h606c.2.2.1
                            have p606_3 := h606c.2.2.2
                            linarith only [hlam, p606_0]
                        · linarith only [h423, h516, h521, h602, h605, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h2, h423, h601, h604, hlam]
                    · linarith only [h4, h515, h603, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h4, h515, h602, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h642 | h642
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h643 | h643
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h644 | h644
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h645 | h645
                        · linarith only [h521, h601, h645, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h4, h515, h516, h521, h645, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h423, h516, h644, hlam]
                    · linarith only [h4, h515, h521, h643, hc35, hlam, hphi, u3ehi1]
                  · linarith only [h4, h515, h642, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h651 | h651
        · linarith only [h0, h4, h651, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h653 | h653
          · linarith only [h0, h423, h653, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h655 | h655
            · rcases m.htr 1 3 5 (by decide) (by decide) with h656 | h656
              · rcases m.htr 1 4 5 (by decide) (by decide) with h657 | h657
                · linarith only [h2, h516, h657, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h659 | h659
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h660 | h660
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h661 | h661
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h662 | h662
                        · linarith only [h2, h516, h655, h662, hlam]
                        · rcases h4bigk with h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h516, h655, h659, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p664_1, u3ehi3]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h423, hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h516, h659, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p664_1, u3ehi3]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h516, hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h2, hlam, p664_1]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h653, hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p664_1, u3ehi3]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h657, hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h0, h423, h659, hc12, hc23, hlam, hphi, p664_1]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h653, h659, hc12, hc23, hlam, hphi, p664_1]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h659, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p664_1, u3ehi3]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h2, h516, h655, h659, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p664_1, u3ehi3]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h515, hlam, p664_1]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h655, hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h659, hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h662, hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h2, h655, hc45, hlam, hphi, ht34, p664_1, u3ehi3]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h655, hc45, hlam, hphi, ht34, p664_1, u3ehi3]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h661, hlam, p664_0]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [h659, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p664_1, u3ehi3]
                          · have p664_0 := h664c.1
                            have p664_1 := h664c.2.1
                            have p664_2 := h664c.2.2.1
                            have p664_3 := h664c.2.2.2
                            linarith only [hlam, p664_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h690 | h690
                        · linarith only [h0, h423, h661, h690, hc12, hc34, hlam, hphi, ht23]
                        · rcases h4bigk with h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h655, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p692_1, u3ehi3]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h423, hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h423, h661, hc45, hlam, hphi, ht34, p692_1, u3ehi3]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h516, hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h2, hlam, p692_1]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h653, hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p692_1, u3ehi3]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h657, hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h661, hc04, hc45, hlam, hphi, p692_1]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h661, hc14, hc45, hlam, hphi, p692_1]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h661, hc45, hlam, hphi, ht34, p692_1, u3ehi3]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h661, hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h515, hlam, p692_1]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h655, hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h659, hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h690, hlam, p692_0]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [hc04, hc45, hlam, hphi, p692_1]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h655, hc45, hlam, hphi, ht34, p692_1, u3ehi3]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [h423, hc02, hc45, hlam, hphi, ht23, ht34, p692_1]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p692_1, u3ehi3]
                          · have p692_0 := h692c.1
                            have p692_1 := h692c.2.1
                            have p692_2 := h692c.2.2.1
                            have p692_3 := h692c.2.2.2
                            linarith only [hlam, p692_0]
                    · linarith only [h1, h4, h656, h660, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1, h4, h656, h659, hc34, hlam, hphi, u3ehi4]
              · linarith only [h655, h656, hc35, hlam, hphi, u3ehi3]
            · linarith only [h515, h516, h655, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h722 | h722
      · rcases m.htr 1 2 3 (by decide) (by decide) with h723 | h723
        · linarith only [h0, h4, h723, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h725 | h725
          · linarith only [h0, h423, h725, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h727 | h727
            · linarith only [h1, h515, h727, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h729 | h729
              · linarith only [h1, h515, h729, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h731 | h731
                · rcases m.htr 2 3 4 (by decide) (by decide) with h732 | h732
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h733 | h733
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h734 | h734
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h735 | h735
                        · rcases h4bigk with h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h729, h731, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p736_1, u3ehi1]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h423, hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h515, hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h515, h732, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p736_1]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h2, hlam, p736_1]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h725, hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h727, hlam, p736_1]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p736_1]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h3, h722, h729, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p736_1, u3ehi1]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h725, hc12, hc24, hlam, hphi, p736_1]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h732, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p736_1, u3ehi3]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            rcases p736_3 (m.d 0 4) (by simp) with h751 | h751
                            · linarith only [h423, h751, hlam]
                            · linarith only [h722, h751, hlam]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h3, h722, h729, hc34, hlam, hphi, p736_1, u3ehi1]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h729, h731, hc34, hlam, hphi, p736_1, u3ehi1]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h732, hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h732, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p736_1]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h722, hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h731, hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h734, hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [h735, hlam, p736_0]
                          · have p736_0 := h736c.1
                            have p736_1 := h736c.2.1
                            have p736_2 := h736c.2.2.1
                            have p736_3 := h736c.2.2.2
                            linarith only [hlam, p736_0]
                        · linarith only [h1, h515, h735, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h0, h2, h423, h731, h734, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1, h515, h732, h733, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h767 | h767
                    · linarith only [h732, h767, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h769 | h769
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h770 | h770
                        · rcases h4bigk with h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h423, h731, h732, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h423, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h515, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            rcases p771_3 (m.d 0 4) (by simp) with h776 | h776
                            · rcases p771_3 (m.d 1 4) (by simp) with h777 | h777
                              · linarith only [h2, h777, hlam]
                              · linarith only [h731, h777, hlam]
                            · linarith only [h776, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h2, hlam, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h725, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h727, hlam, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h423, h732, hc02, hc34, hlam, hphi, ht23, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h725, h732, hc12, hc34, hlam, hphi, ht23, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h732, hlam, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            rcases p771_3 (m.d 0 4) (by simp) with h790 | h790
                            · linarith only [h423, h790, hlam]
                            · linarith only [h722, h790, hlam]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h3, h722, h729, hc34, hlam, hphi, p771_1, u3ehi1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h729, h731, hc34, hlam, hphi, p771_1, u3ehi1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h0, h423, hc12, hc34, hlam, hphi, ht23, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            rcases p771_3 (m.d 0 4) (by simp) with h797 | h797
                            · linarith only [h515, h797, hlam]
                            · linarith only [h722, h797, hlam]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h722, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h731, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h769, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h770, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hlam, p771_0]
                        · linarith only [h1, h515, h770, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h2, h3, h423, h722, h729, h731, h769, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h515, h722, h727, h731, hc34, hlam, hphi, u3ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h808 | h808
        · linarith only [h0, h4, h808, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h810 | h810
          · linarith only [h0, h423, h810, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h812 | h812
            · linarith only [h1, h515, h722, h812, hc45, hlam, hphi, ht34, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h814 | h814
              · linarith only [h1, h515, h722, h814, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h816 | h816
                · linarith only [h2, h515, h722, h816, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h818 | h818
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h819 | h819
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h820 | h820
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h821 | h821
                        · linarith only [h1, h515, h722, h821, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h1, h515, h818, h820, h821, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1, h515, h818, h820, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h1, h515, h818, h819, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h826 | h826
                    · linarith only [h818, h826, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h828 | h828
                      · linarith only [h1, h515, h722, h818, h828, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h830 | h830
                        · linarith only [h4, h818, h828, h830, hc02, hc34, hlam, hphi, ht23]
                        · linarith only [h1, h515, h830, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_13_24_L_R_H_I_x0_x0_x0_x0_x0 m hb3 hb4 h0 h1 h2 h3 h4
  · exact r1l7_13_24_L_R_H_I_x0_x0_x0_x0_x1 m hb3 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h833 | h833
  · rcases m.htr 0 2 4 (by decide) (by decide) with h834 | h834
    · rcases m.htr 0 3 4 (by decide) (by decide) with h835 | h835
      · rcases m.htr 0 4 5 (by decide) (by decide) with h836 | h836
        · linarith only [h2, h3, h836, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h838 | h838
          · linarith only [h0, h3, h838, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h840 | h840
            · linarith only [h0, h3, h833, h838, h840, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h842 | h842
              · linarith only [h1, h3, h842, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h1, h3, h835, h842, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h845 | h845
        · linarith only [h2, h3, h845, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h847 | h847
          · linarith only [h0, h3, h847, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h849 | h849
            · linarith only [h0, h3, h833, h847, h849, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h851 | h851
              · linarith only [h1, h3, h851, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h853 | h853
                · linarith only [h0, h3, h834, h849, h851, h853, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h3, h833, h847, h853, hc12, hc35, hlam, hphi, ht23]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h856 | h856
      · linarith only [h833, h834, h856, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h858 | h858
        · linarith only [h2, h3, h858, hlam]
        · linarith only [h833, h834, h858, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h861 | h861
    · rcases m.htr 0 3 4 (by decide) (by decide) with h862 | h862
      · rcases m.htr 0 4 5 (by decide) (by decide) with h863 | h863
        · linarith only [h1, h3, h833, h861, h863, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h865 | h865
          · linarith only [h0, h3, h833, h865, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h867 | h867
            · rcases m.htr 1 3 4 (by decide) (by decide) with h868 | h868
              · linarith only [h1, h3, h868, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h1, h3, h862, h868, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h833, h861, h867, hc12, hc23, hlam, hphi]
      · linarith only [h833, h861, h862, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h873 | h873
      · rcases m.htr 0 4 5 (by decide) (by decide) with h874 | h874
        · linarith only [h1, h3, h873, h874, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h876 | h876
          · linarith only [h0, h833, h876, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h878 | h878
            · linarith only [h1, h3, h861, h876, h878, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h880 | h880
              · linarith only [h1, h3, h880, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h1, h3, h873, h880, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h883 | h883
        · linarith only [h2, h3, h883, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h885 | h885
          · linarith only [h0, h3, h885, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h887 | h887
            · linarith only [h0, h3, h861, h887, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h889 | h889
              · linarith only [h1, h3, h889, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h891 | h891
                · linarith only [h2, h3, h889, h891, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h2, h3, h889, h891, hc35, hlam, hphi, u3ehi1]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_13_24_L_R_H_I_x0_x0_x0_x0 m hb3 hb4 h0 h1 h2 h3
  · exact r1l7_13_24_L_R_H_I_x0_x0_x0_x1 m hb3 hb4 h0 h1 h2 h3

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h894 | h894
  · rcases m.htr 0 2 3 (by decide) (by decide) with h895 | h895
    · rcases m.htr 0 2 4 (by decide) (by decide) with h896 | h896
      · linarith only [h0, h2, h896, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h898 | h898
        · linarith only [h0, h2, h895, h898, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
          · rcases m.htr 1 2 3 (by decide) (by decide) with h901 | h901
            · linarith only [h0, h2, h901, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h895, h896, h901, hc12, hc24, hlam, hphi]
          · linarith only [h0, h2, h895, h900, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h905 | h905
      · linarith only [h1, h2, h895, h905, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h907 | h907
        · linarith only [h1, h2, h907, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h909 | h909
          · rcases m.htr 1 2 3 (by decide) (by decide) with h910 | h910
            · linarith only [h0, h2, h895, h910, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h912 | h912
              · linarith only [h0, h2, h905, h912, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h914 | h914
                · linarith only [h1, h2, h895, h907, h912, h914, hc02, hc24, hlam, hphi]
                · linarith only [h1, h2, h914, hc34, hlam, hphi, u3ehi1]
          · linarith only [h1, h2, h909, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h918 | h918
    · rcases m.htr 0 2 4 (by decide) (by decide) with h919 | h919
      · linarith only [h0, h2, h919, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h921 | h921
        · linarith only [h0, h2, h918, h921, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h923 | h923
          · rcases m.htr 1 2 3 (by decide) (by decide) with h924 | h924
            · linarith only [h0, h2, h924, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h918, h919, h924, hc12, hc24, hlam, hphi]
          · linarith only [h0, h2, h918, h923, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h928 | h928
      · linarith only [h1, h2, h918, h928, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h930 | h930
        · linarith only [h1, h2, h930, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h932 | h932
          · rcases m.htr 1 2 3 (by decide) (by decide) with h933 | h933
            · linarith only [h0, h894, h918, h933, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h935 | h935
              · linarith only [h0, h894, h928, h932, h935, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h937 | h937
                · linarith only [h1, h2, h918, h930, h935, h937, hc02, hc24, hlam, hphi]
                · linarith only [h1, h2, h937, hc34, hlam, hphi, u3ehi1]
          · linarith only [h1, h2, h932, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_13_24_L_R_H_I_x0_x0_x0 m hb3 hb4 h0 h1 h2
  · exact r1l7_13_24_L_R_H_I_x0_x0_x1 m hb3 hb4 h0 h1 h2

end R2N4
