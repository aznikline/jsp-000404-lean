import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_73S8

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_14_M_LI_L_0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h475 | h475
  · rcases m.htr 0 1 4 (by decide) (by decide) with h476 | h476
    · rcases m.htr 0 1 5 (by decide) (by decide) with h477 | h477
      · rcases m.htr 1 2 3 (by decide) (by decide) with h478 | h478
        · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
          · rcases m.htr 1 2 5 (by decide) (by decide) with h480 | h480
            · rcases m.htr 1 3 4 (by decide) (by decide) with h481 | h481
              · linarith only [h0, h475, h481, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h483 | h483
                · linarith only [h0, h476, h481, h483, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h485 | h485
                  · linarith only [h0, h476, h485, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
                    · linarith only [h479, h485, h487, hlam]
                    · rcases h1bigk with h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h0, hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo1]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p489_1, u1elo1]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p489_1, u1elo1]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [hc01, hlam, hphi, p489_1, u1elo1]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        rcases p489_3 (m.d 0 1) (by simp) with h497 | h497
                        · linarith only [h0, h497, hlam]
                        · linarith only [h475, h497, hlam]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        rcases p489_3 (m.d 0 1) (by simp) with h500 | h500
                        · linarith only [h0, h500, hlam]
                        · linarith only [h476, h500, hlam]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        rcases p489_3 (m.d 0 1) (by simp) with h503 | h503
                        · linarith only [h0, h503, hlam]
                        · linarith only [h477, h503, hlam]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h475, hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h478, hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h481, hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h483, hlam, p489_1]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h476, hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h479, hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h478, h485, hc23, hlam, hphi, ht34, p489_1, u4elo4]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h485, hlam, p489_1]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h477, hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h480, hlam, p489_0]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h0, h477, h478, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo1]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [h0, h477, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p489_1, u1elo1]
                      · have p489_0 := h489c.1
                        have p489_1 := h489c.2.1
                        have p489_2 := h489c.2.2.1
                        have p489_3 := h489c.2.2.2
                        linarith only [hlam, p489_0]
            · linarith only [h0, h477, h480, hlam]
          · linarith only [h0, h479, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h0, h475, h478, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h524 | h524
        · rcases m.htr 1 2 4 (by decide) (by decide) with h525 | h525
          · rcases m.htr 1 2 5 (by decide) (by decide) with h526 | h526
            · rcases m.htr 1 3 4 (by decide) (by decide) with h527 | h527
              · linarith only [h475, h477, h526, h527, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h529 | h529
                · linarith only [h476, h477, h526, h527, h529, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h531 | h531
                  · linarith only [h476, h477, h526, h531, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h476, h477, h524, h527, h531, hc23, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h534 | h534
              · linarith only [h0, h475, h526, h534, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
                · linarith only [h0, h476, h526, h534, h536, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h538 | h538
                  · linarith only [h0, h476, h526, h538, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h476, h524, h526, h534, h538, hc23, hlam, hphi, ht34, u4elo4]
          · linarith only [h0, h475, h524, h525, hc23, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h475, h524, hlam]
    · linarith only [h475, h476, hc13, hlam, hphi, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h544 | h544
    · rcases m.htr 0 1 5 (by decide) (by decide) with h545 | h545
      · rcases m.htr 1 2 3 (by decide) (by decide) with h546 | h546
        · rcases m.htr 1 2 4 (by decide) (by decide) with h547 | h547
          · rcases m.htr 1 2 5 (by decide) (by decide) with h548 | h548
            · rcases m.htr 1 3 4 (by decide) (by decide) with h549 | h549
              · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
                · rcases m.htr 1 4 5 (by decide) (by decide) with h551 | h551
                  · linarith only [h475, h544, h551, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h553 | h553
                    · linarith only [h547, h551, h553, hlam]
                    · rcases h1bigk with h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h0, hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h475, hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h475, h546, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p555_1, u1elo1]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h475, h546, hc15, hlam, hphi, ht01, ht0b, ht5b, p555_1, u1elo1]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [hc01, hlam, hphi, p555_1, u1elo1]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h475, hc01, hlam, hphi, p555_1, u1elo1]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        rcases p555_3 (m.d 0 1) (by simp) with h564 | h564
                        · linarith only [h0, h564, hlam]
                        · linarith only [h544, h564, hlam]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        rcases p555_3 (m.d 0 1) (by simp) with h567 | h567
                        · linarith only [h0, h567, hlam]
                        · linarith only [h545, h567, hlam]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h545, h547, h551, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p555_1, u1elo2]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h546, hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        rcases p555_3 (m.d 0 1) (by simp) with h573 | h573
                        · linarith only [h475, h573, hlam]
                        · linarith only [h544, h573, hlam]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        rcases p555_3 (m.d 0 1) (by simp) with h576 | h576
                        · linarith only [h475, h576, hlam]
                        · linarith only [h545, h576, hlam]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h544, hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h547, hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h549, hlam, p555_1]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h551, hlam, p555_1]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h545, hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h548, hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h550, hlam, p555_0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [h545, h547, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p555_1, u1elo0]
                      · have p555_0 := h555c.1
                        have p555_1 := h555c.2.1
                        have p555_2 := h555c.2.2.1
                        have p555_3 := h555c.2.2.2
                        linarith only [hlam, p555_0]
                · linarith only [h475, h545, h550, hlam]
              · linarith only [h475, h549, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h475, h545, h546, h548, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
          · linarith only [h475, h546, h547, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h593 | h593
          · rcases m.htr 1 2 5 (by decide) (by decide) with h594 | h594
            · rcases m.htr 1 3 4 (by decide) (by decide) with h595 | h595
              · rcases m.htr 1 3 5 (by decide) (by decide) with h596 | h596
                · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
                  · linarith only [h0, h544, h597, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h599 | h599
                    · linarith only [h593, h597, h599, hlam]
                    · rcases h1bigk with h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h475, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h546, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p601_1, u1elo2]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h546, hc15, hlam, hphi, ht01, ht0b, ht5b, p601_1, u1elo2]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h546, hc01, hlam, hphi, p601_1, u1elo2]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h546, hlam, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        rcases p601_3 (m.d 0 1) (by simp) with h610 | h610
                        · linarith only [h0, h610, hlam]
                        · linarith only [h544, h610, hlam]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        rcases p601_3 (m.d 0 1) (by simp) with h613 | h613
                        · linarith only [h0, h613, hlam]
                        · linarith only [h545, h613, hlam]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h545, h594, h599, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p601_1, u1elo2]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h545, h594, h599, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p601_1, u1elo2]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        rcases p601_3 (m.d 0 1) (by simp) with h619 | h619
                        · linarith only [h475, h619, hlam]
                        · linarith only [h544, h619, hlam]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        rcases p601_3 (m.d 0 1) (by simp) with h622 | h622
                        · linarith only [h475, h622, hlam]
                        · linarith only [h545, h622, hlam]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h544, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h593, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h595, hlam, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h597, hlam, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h545, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h594, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h596, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h545, h546, h593, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                · linarith only [h0, h545, h546, h596, hlam]
              · linarith only [h0, h546, h595, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h0, h545, h594, hlam]
          · linarith only [h0, h593, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h639 | h639
        · rcases m.htr 1 2 4 (by decide) (by decide) with h640 | h640
          · rcases m.htr 1 2 5 (by decide) (by decide) with h641 | h641
            · rcases m.htr 1 3 4 (by decide) (by decide) with h642 | h642
              · rcases m.htr 1 3 5 (by decide) (by decide) with h643 | h643
                · rcases m.htr 1 4 5 (by decide) (by decide) with h644 | h644
                  · linarith only [h544, h545, h639, h643, h644, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h544, h545, h644, hc14, hlam, hphi, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h647 | h647
                  · linarith only [h0, h544, h647, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h544, h545, h642, h647, hc34, hlam, hphi, u4elo4]
              · linarith only [h475, h544, h640, h642, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h651 | h651
              · rcases m.htr 1 3 5 (by decide) (by decide) with h652 | h652
                · linarith only [h639, h641, h652, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h654 | h654
                  · linarith only [h0, h544, h654, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h544, h545, h640, h654, hc24, hlam, hphi, u4elo4]
              · linarith only [h475, h544, h640, h651, hc24, hlam, hphi, u4elo3]
          · linarith only [h475, h639, h640, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h659 | h659
          · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
            · rcases m.htr 1 3 4 (by decide) (by decide) with h661 | h661
              · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
                · rcases m.htr 1 4 5 (by decide) (by decide) with h663 | h663
                  · linarith only [h544, h545, h660, h663, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h544, h545, h663, hc14, hlam, hphi, u4elo4]
                · linarith only [h639, h660, h662, hlam]
              · linarith only [h544, h545, h639, h659, h660, h661, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h668 | h668
              · rcases m.htr 1 3 5 (by decide) (by decide) with h669 | h669
                · rcases m.htr 1 4 5 (by decide) (by decide) with h670 | h670
                  · linarith only [h0, h544, h660, h669, h670, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · linarith only [h0, h544, h660, h670, hc14, hlam, hphi, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h673 | h673
                  · linarith only [h0, h544, h639, h669, h673, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h0, h544, h639, h668, h669, h673, hc34, hlam, hphi, u4elo4]
              · linarith only [h0, h544, h639, h668, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h544, h659, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h678 | h678
      · rcases m.htr 1 2 3 (by decide) (by decide) with h679 | h679
        · rcases m.htr 1 2 4 (by decide) (by decide) with h680 | h680
          · rcases m.htr 1 2 5 (by decide) (by decide) with h681 | h681
            · rcases m.htr 1 3 4 (by decide) (by decide) with h682 | h682
              · rcases m.htr 1 3 5 (by decide) (by decide) with h683 | h683
                · rcases m.htr 1 4 5 (by decide) (by decide) with h684 | h684
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h685 | h685
                    · rcases h1bigk with h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h0, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h475, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h544, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h544, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p686_1, u4elo1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hc01, hlam, hphi, p686_1, u1elo1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h544, h678, h681, h682, h685, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p686_1, u1elo1, u4elo1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h544, h678, h681, h685, hc45, hlam, hphi, ht01, ht0b, ht5b, p686_1, u1elo1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        rcases p686_3 (m.d 0 1) (by simp) with h696 | h696
                        · linarith only [h0, h696, hlam]
                        · linarith only [h678, h696, hlam]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h678, h681, h685, hc45, hlam, hphi, ht01, ht0b, ht5b, p686_1, u1elo2]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h679, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h544, h678, h679, h681, h685, hc45, hlam, hphi, ht01, ht0b, ht5b, p686_1, u1elo1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        rcases p686_3 (m.d 0 1) (by simp) with h703 | h703
                        · linarith only [h475, h703, hlam]
                        · linarith only [h678, h703, hlam]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h678, h681, h685, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p686_1, u4elo1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h680, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h682, hlam, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        rcases p686_3 (m.d 0 1) (by simp) with h710 | h710
                        · linarith only [h544, h710, hlam]
                        · linarith only [h678, h710, hlam]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h678, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h681, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h683, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h684, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                    · linarith only [h684, h685, hc24, hlam, hphi, u4elo1]
                  · linarith only [h544, h684, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h544, h678, h682, h683, hlam]
              · linarith only [h475, h678, h681, h682, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
            · linarith only [h475, h678, h679, h681, hlam]
          · linarith only [h475, h679, h680, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h724 | h724
          · rcases m.htr 1 2 5 (by decide) (by decide) with h725 | h725
            · rcases m.htr 1 3 4 (by decide) (by decide) with h726 | h726
              · rcases m.htr 1 3 5 (by decide) (by decide) with h727 | h727
                · rcases m.htr 1 4 5 (by decide) (by decide) with h728 | h728
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h729 | h729
                    · rcases h1bigk with h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h0, hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h475, hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h544, hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h544, h725, h729, hc45, hlam, hphi, ht01, ht0b, ht5b, p730_1, u1elo3]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h679, hc01, hlam, hphi, p730_1, u1elo2]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h679, hlam, p730_1]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h544, h678, h679, h725, h729, hc45, hlam, hphi, ht01, ht0b, ht5b, p730_1, u1elo2]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        rcases p730_3 (m.d 0 1) (by simp) with h740 | h740
                        · linarith only [h0, h740, hlam]
                        · linarith only [h678, h740, hlam]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h678, h725, h729, hc45, hlam, hphi, ht01, ht0b, ht5b, p730_1, u1elo2]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h724, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p730_1, u1elo2]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h544, h678, h725, h729, hc45, hlam, hphi, ht01, ht0b, ht5b, p730_1, u1elo2]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        rcases p730_3 (m.d 0 1) (by simp) with h747 | h747
                        · linarith only [h475, h747, hlam]
                        · linarith only [h678, h747, hlam]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h678, h725, h729, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p730_1, u4elo1]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h724, hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h726, hlam, p730_1]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        rcases p730_3 (m.d 0 1) (by simp) with h754 | h754
                        · linarith only [h544, h754, hlam]
                        · linarith only [h678, h754, hlam]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h678, hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h725, hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h727, hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [h728, hlam, p730_0]
                      · have p730_0 := h730c.1
                        have p730_1 := h730c.2.1
                        have p730_2 := h730c.2.2.1
                        have p730_3 := h730c.2.2.2
                        linarith only [hlam, p730_0]
                    · linarith only [h728, h729, hc24, hlam, hphi, u4elo1]
                  · linarith only [h544, h728, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h544, h678, h726, h727, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
              · linarith only [h544, h678, h679, h724, h725, h726, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
            · linarith only [h544, h678, h724, h725, hlam]
          · linarith only [h0, h724, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h768 | h768
        · rcases m.htr 1 2 4 (by decide) (by decide) with h769 | h769
          · rcases m.htr 1 2 5 (by decide) (by decide) with h770 | h770
            · rcases m.htr 1 3 4 (by decide) (by decide) with h771 | h771
              · rcases m.htr 1 3 5 (by decide) (by decide) with h772 | h772
                · rcases m.htr 1 4 5 (by decide) (by decide) with h773 | h773
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h774 | h774
                    · rcases h1bigk with h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h0, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h475, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h544, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h678, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hc01, hlam, hphi, p775_1, u1elo1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h678, h771, h773, hc01, hlam, hphi, p775_1, u1elo1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h678, h773, hc01, hlam, hphi, p775_1, u1elo1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h678, hc01, hlam, hphi, p775_1, u1elo1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hc01, hlam, hphi, p775_1, u1elo2]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h768, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h678, h768, h773, hc01, hlam, hphi, p775_1, u1elo1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h678, h768, hc01, hlam, hphi, p775_1, u1elo1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hc01, hlam, hphi, p775_1, u1elo3]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h769, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h771, hlam, p775_1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h678, hc01, hlam, hphi, ht12, ht23, ht34, p775_1, u4elo1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hc01, hlam, hphi, p775_1, u1elo4]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h770, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h772, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h773, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hlam, p775_0]
                    · linarith only [h773, h774, hc24, hlam, hphi, u4elo1]
                  · linarith only [h544, h773, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h803 | h803
                  · linarith only [h771, h772, h803, hlam]
                  · linarith only [h544, h803, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h475, h771, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h807 | h807
              · rcases m.htr 1 3 5 (by decide) (by decide) with h808 | h808
                · linarith only [h768, h770, h808, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h810 | h810
                  · linarith only [h769, h770, h810, hlam]
                  · linarith only [h544, h810, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h475, h807, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h475, h768, h769, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h815 | h815
          · rcases m.htr 1 2 5 (by decide) (by decide) with h816 | h816
            · rcases m.htr 1 3 4 (by decide) (by decide) with h817 | h817
              · rcases m.htr 1 3 5 (by decide) (by decide) with h818 | h818
                · rcases m.htr 1 4 5 (by decide) (by decide) with h819 | h819
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h820 | h820
                    · rcases h1bigk with h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h0, hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h475, hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h544, hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h678, hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [hc01, hlam, hphi, p821_1, u1elo1]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h768, hlam, p821_1]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h544, h768, hc01, hlam, hphi, p821_1, u1elo2]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h678, h768, hc01, hlam, hphi, p821_1, u1elo2]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [hc01, hlam, hphi, p821_1, u1elo2]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h815, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p821_1, u1elo2]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h678, h819, hc01, hlam, hphi, p821_1, u1elo2]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h678, hc01, hlam, hphi, p821_1, u1elo2]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [hc01, hlam, hphi, p821_1, u1elo3]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h815, hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h817, hlam, p821_1]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h678, h815, hc01, hlam, hphi, p821_1, u1elo1]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [hc01, hlam, hphi, p821_1, u1elo4]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h816, hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h818, hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [h819, hlam, p821_0]
                      · have p821_0 := h821c.1
                        have p821_1 := h821c.2.1
                        have p821_2 := h821c.2.2.1
                        have p821_3 := h821c.2.2.2
                        linarith only [hlam, p821_0]
                    · linarith only [h819, h820, hc24, hlam, hphi, u4elo1]
                  · linarith only [h544, h819, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h768, h816, h818, hlam]
              · linarith only [h0, h768, h817, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h851 | h851
              · rcases m.htr 1 3 5 (by decide) (by decide) with h852 | h852
                · rcases m.htr 1 4 5 (by decide) (by decide) with h853 | h853
                  · linarith only [h815, h816, h853, hlam]
                  · linarith only [h544, h853, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h856 | h856
                  · linarith only [h768, h815, h852, h856, hlam]
                  · linarith only [h544, h856, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h544, h768, h815, h851, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h0, h815, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

theorem r1l7_21_14_M_LI_L_0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_14_M_LI_L_0_x0 m hb1 hb4 h0
  · exact r1l7_21_14_M_LI_L_0_x1 m hb1 hb4 h0

end R2N4
