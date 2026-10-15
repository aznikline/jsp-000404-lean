import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_63S6

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_24_L_0_H_I_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h1 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h492 | h492
  · rcases m.htr 0 2 5 (by decide) (by decide) with h493 | h493
    · rcases m.htr 0 3 4 (by decide) (by decide) with h494 | h494
      · rcases m.htr 0 4 5 (by decide) (by decide) with h495 | h495
        · rcases m.htr 1 2 4 (by decide) (by decide) with h496 | h496
          · rcases m.htr 1 2 5 (by decide) (by decide) with h497 | h497
            · rcases m.htr 1 4 5 (by decide) (by decide) with h498 | h498
              · rcases m.htr 2 3 4 (by decide) (by decide) with h499 | h499
                · rcases m.htr 2 4 5 (by decide) (by decide) with h500 | h500
                  · linarith only [h1, h492, h500, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h1, h492, h495, h500, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h0, h1, h492, h494, h498, h499, hc03, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h1, h492, h495, h498, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h1, h493, h496, h497, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h1, h492, h496, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h507 | h507
          · rcases m.htr 1 2 5 (by decide) (by decide) with h508 | h508
            · rcases m.htr 1 4 5 (by decide) (by decide) with h509 | h509
              · linarith only [h0, h495, h509, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h511 | h511
                · rcases m.htr 2 4 5 (by decide) (by decide) with h512 | h512
                  · linarith only [h0, h495, h507, h512, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h514 | h514
                    · linarith only [h0, h495, h507, h511, h514, hlam]
                    · rcases h4bigk with h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h495, h507, h511, hc34, hc45, hlam, hphi, p516_1]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h1, h492, h511, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p516_1, u2elo2]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h1, h493, h495, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p516_1, u2elo2]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h495, hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h0, hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h0, h511, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p516_1]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h0, h1, h493, h495, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p516_1, u2elo2]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h509, hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h492, hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h507, hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p516_1, u2elo3]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h512, hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h494, hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h1, h494, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p516_1, u2elo2]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h511, hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h514, hlam, p516_0]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p516_1]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [hc14, hc45, hlam, hphi, p516_1]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [h511, hc34, hc45, hlam, hphi, p516_1]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [hc34, hc45, hlam, hphi, p516_1]
                      · have p516_0 := h516c.1
                        have p516_1 := h516c.2.1
                        have p516_2 := h516c.2.2.1
                        have p516_3 := h516c.2.2.2
                        linarith only [hlam, p516_0]
                · linarith only [h1, h494, h511, hlam]
            · linarith only [h1, h493, h508, hc12, hlam, hphi, u2elo2]
          · linarith only [h1, h492, h507, hc12, hlam, hphi, u2elo2]
      · linarith only [h1, h492, h494, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h546 | h546
      · rcases m.htr 0 4 5 (by decide) (by decide) with h547 | h547
        · linarith only [h492, h493, h547, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h549 | h549
          · rcases m.htr 1 2 5 (by decide) (by decide) with h550 | h550
            · linarith only [h493, h550, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h552 | h552
              · linarith only [h0, h547, h552, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h554 | h554
                · rcases m.htr 2 4 5 (by decide) (by decide) with h555 | h555
                  · linarith only [h0, h492, h547, h555, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h557 | h557
                    · linarith only [h550, h554, h555, h557, hc12, hlam, hphi, u2elo3]
                    · rcases h4bigk with h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h1, h492, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p559_1, u2elo2]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h1, h492, h554, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p559_1, u2elo2]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h1, h492, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p559_1, u2elo2]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h547, hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h0, hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h0, h554, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p559_1]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h549, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p559_1, u2elo1]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h552, hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h492, hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h549, hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p559_1, u2elo3]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h555, hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h546, hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h546, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p559_1]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h554, hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h557, hlam, p559_0]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p559_1]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h549, hc24, hc45, hlam, hphi, p559_1]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [h554, hc34, hc45, hlam, hphi, p559_1]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [hc34, hc45, hlam, hphi, p559_1]
                      · have p559_0 := h559c.1
                        have p559_1 := h559c.2.1
                        have p559_2 := h559c.2.2.1
                        have p559_3 := h559c.2.2.2
                        linarith only [hlam, p559_0]
                · linarith only [h1, h546, h554, hlam]
          · linarith only [h1, h492, h549, hc12, hlam, hphi, u2elo2]
      · linarith only [h1, h492, h546, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h588 | h588
    · rcases m.htr 0 3 4 (by decide) (by decide) with h589 | h589
      · rcases m.htr 0 4 5 (by decide) (by decide) with h590 | h590
        · rcases m.htr 1 2 4 (by decide) (by decide) with h591 | h591
          · linarith only [h492, h591, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h593 | h593
            · rcases m.htr 1 4 5 (by decide) (by decide) with h594 | h594
              · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                · rcases m.htr 2 4 5 (by decide) (by decide) with h596 | h596
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h597 | h597
                    · rcases h4bigk with h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h591, h593, h596, hc04, hc45, hlam, hphi, ht0b, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h492, hlam, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h589, h597, hc03, hc45, hlam, hphi, ht0b, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h1, h589, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p598_1, u2elo2]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h0, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h591, hlam, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h597, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h0, h1, h589, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p598_1, u2elo2]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h595, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p598_1, u2elo2]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h595, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p598_1, u2elo2]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h595, h597, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p598_1, u2elo2]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h595, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p598_1, u2elo2]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h589, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h591, h593, h596, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h595, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h1, h589, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p598_1, u2elo2]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h590, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h594, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h596, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h597, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [hlam, p598_0]
                    · linarith only [h1, h588, h596, h597, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h492, h590, h596, hlam]
                · linarith only [h1, h589, h595, hlam]
              · linarith only [h1, h589, h590, h591, h594, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h588, h593, hc12, hlam, hphi, u2elo2]
        · linarith only [h492, h588, h590, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h630 | h630
        · rcases m.htr 1 2 4 (by decide) (by decide) with h631 | h631
          · linarith only [h492, h631, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h633 | h633
            · rcases m.htr 1 4 5 (by decide) (by decide) with h634 | h634
              · rcases m.htr 2 3 4 (by decide) (by decide) with h635 | h635
                · linarith only [h1, h588, h589, h635, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h638 | h638
                    · rcases h4bigk with h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [hlam, p639_0]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h631, h633, h637, hc04, hc45, hlam, hphi, ht0b, ht5b, p639_1]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h492, hlam, p639_1]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h589, hlam, p639_1]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h492, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p639_1, u2elo3]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h0, hlam, p639_0]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [hlam, p639_0]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h631, hlam, p639_1]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h1, h588, h635, h637, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p639_1]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h0, h492, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p639_1, u2elo3]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p639_1, u2elo3]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p639_1, u2elo3]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [hlam, p639_0]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h635, hlam, p639_1]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p639_1, u2elo3]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h1, h588, h589, h637, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p639_1]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h631, h633, h637, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p639_1]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h492, h588, h637, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p639_1]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [hlam, p639_0]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        rcases p639_3 (m.d 0 4) (by simp) with h659 | h659
                        · linarith only [h589, h659, hlam]
                        · linarith only [h630, h659, hlam]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h630, hlam, p639_0]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h634, hlam, p639_0]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h637, hlam, p639_0]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [h638, hlam, p639_0]
                      · have p639_0 := h639c.1
                        have p639_1 := h639c.2.1
                        have p639_2 := h639c.2.2.1
                        have p639_3 := h639c.2.2.2
                        linarith only [hlam, p639_0]
                    · linarith only [h1, h588, h637, h638, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1, h588, h630, h635, h637, hc04, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h1, h588, h630, h631, h633, h634, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h1, h588, h633, hc12, hlam, hphi, u2elo2]
        · linarith only [h492, h588, h630, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h672 | h672
      · rcases m.htr 0 4 5 (by decide) (by decide) with h673 | h673
        · rcases m.htr 1 2 4 (by decide) (by decide) with h674 | h674
          · linarith only [h492, h674, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h676 | h676
            · linarith only [h588, h676, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h678 | h678
              · rcases m.htr 2 3 4 (by decide) (by decide) with h679 | h679
                · rcases m.htr 2 4 5 (by decide) (by decide) with h680 | h680
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h681 | h681
                    · rcases h4bigk with h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h1, h672, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p682_1, u2elo2]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h492, hlam, p682_1]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h1, h672, h681, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p682_1, u2elo2]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h1, h672, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p682_1, u2elo2]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h0, hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h674, hlam, p682_1]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h681, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p682_1]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h0, h1, h672, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p682_1, u2elo2]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h679, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p682_1, u2elo2]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h679, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p682_1, u2elo2]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h679, h681, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p682_1, u2elo2]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h679, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p682_1, u2elo2]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h672, hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h676, h678, hc12, hc34, hlam, hphi, ht23, p682_1]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h679, hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h1, h672, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p682_1, u2elo2]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h673, hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h678, hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h680, hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [h681, hlam, p682_0]
                      · have p682_0 := h682c.1
                        have p682_1 := h682c.2.1
                        have p682_2 := h682c.2.2.1
                        have p682_3 := h682c.2.2.2
                        linarith only [hlam, p682_0]
                    · rcases h4bigk with h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h678, h681, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p708_1]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h492, hlam, p708_1]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h492, h679, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p708_1, u2elo2]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h492, h679, h681, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p708_1, u2elo2]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h0, hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h674, hlam, p708_1]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p708_1]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h681, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p708_1]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h679, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p708_1, u2elo2]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h679, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p708_1, u2elo2]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h679, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p708_1, u2elo2]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h679, h681, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p708_1, u2elo2]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h672, hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h678, h681, hlam, p708_1]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h679, hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h681, hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h673, hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h678, hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h680, hlam, p708_0]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [h678, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p708_1]
                      · have p708_0 := h708c.1
                        have p708_1 := h708c.2.1
                        have p708_2 := h708c.2.2.1
                        have p708_3 := h708c.2.2.2
                        linarith only [hlam, p708_0]
                  · linarith only [h0, h492, h678, h680, hlam]
                · linarith only [h1, h672, h679, hlam]
              · linarith only [h1, h672, h673, h674, h678, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h737 | h737
          · linarith only [h492, h737, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h739 | h739
            · linarith only [h492, h588, h673, h737, h739, hc02, hlam, hphi, u2elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h741 | h741
              · linarith only [h0, h673, h741, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h743 | h743
                · rcases m.htr 2 4 5 (by decide) (by decide) with h744 | h744
                  · linarith only [h0, h673, h737, h743, h744, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h746 | h746
                    · linarith only [h492, h744, h746, hc02, hc34, hlam, hphi, ht23]
                    · rcases h4bigk with h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h492, h737, hc12, hlam, hphi, p748_1, u2elo3]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h492, hlam, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h492, h744, hc34, hc45, hlam, hphi, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h673, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h0, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h737, hlam, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h741, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h744, hc04, hc45, hlam, hphi, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h744, hc14, hc45, hlam, hphi, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h744, hc34, hc45, hlam, hphi, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h744, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h672, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h737, hc12, hc34, hlam, hphi, ht23, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h743, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h746, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h0, h737, hc12, hc45, hlam, hphi, ht23, ht34, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h737, hc12, hc45, hlam, hphi, ht23, ht34, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hc24, hc45, hlam, hphi, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hc34, hc45, hlam, hphi, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hlam, p748_0]
                · linarith only [h1, h672, h743, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h775 | h775
        · rcases m.htr 1 2 4 (by decide) (by decide) with h776 | h776
          · linarith only [h492, h776, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h778 | h778
            · linarith only [h588, h776, h778, hc02, hlam, hphi, u2elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h780 | h780
              · rcases m.htr 2 3 4 (by decide) (by decide) with h781 | h781
                · linarith only [h1, h672, h781, hc02, hlam, hphi, u2elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h783 | h783
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h784 | h784
                    · rcases h4bigk with h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [hlam, p785_0]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h780, hc04, hc45, hlam, hphi, ht0b, ht5b, p785_1]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h492, hlam, p785_1]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h672, hlam, p785_1]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h492, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p785_1, u2elo3]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h0, hlam, p785_0]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [hlam, p785_0]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h776, hlam, p785_1]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h781, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p785_1]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p785_1]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p785_1, u2elo3]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p785_1, u2elo3]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [hlam, p785_0]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h781, hlam, p785_1]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p785_1, u2elo3]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h0, h780, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p785_1]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h780, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p785_1]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h492, hc02, hc34, hlam, hphi, ht23, p785_1]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [hlam, p785_0]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        rcases p785_3 (m.d 0 4) (by simp) with h805 | h805
                        · linarith only [h672, h805, hlam]
                        · linarith only [h775, h805, hlam]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h775, hlam, p785_0]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h780, hlam, p785_0]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h783, hlam, p785_0]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [h784, hlam, p785_0]
                      · have p785_0 := h785c.1
                        have p785_1 := h785c.2.1
                        have p785_2 := h785c.2.2.1
                        have p785_3 := h785c.2.2.2
                        linarith only [hlam, p785_0]
                    · linarith only [h0, h1, h492, h672, h780, h784, hc02, hlam, hphi, u2elo3]
                  · linarith only [h0, h492, h780, h783, hlam]
              · linarith only [h492, h775, h776, h780, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h816 | h816
          · linarith only [h492, h816, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h818 | h818
            · linarith only [h0, h588, h775, h816, h818, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h820 | h820
              · linarith only [h0, h775, h820, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h822 | h822
                · linarith only [h1, h672, h822, hc02, hlam, hphi, u2elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h824 | h824
                  · linarith only [h0, h775, h816, h824, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h826 | h826
                    · linarith only [h492, h824, h826, hc02, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h822, h826, hc02, hc45, hlam, hphi, ht23, ht34]

theorem r1l7_12_24_L_0_H_I_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_12_24_L_0_H_I_x0_x0 m hb2 hb4 h0 h1
  · exact r1l7_12_24_L_0_H_I_x0_x1 m hb2 hb4 h0 h1

end R2N4
