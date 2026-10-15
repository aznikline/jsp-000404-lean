import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h541 | h541
  · rcases m.htr 0 4 5 (by decide) (by decide) with h542 | h542
    · rcases m.htr 1 2 3 (by decide) (by decide) with h543 | h543
      · rcases m.htr 1 2 4 (by decide) (by decide) with h544 | h544
        · rcases m.htr 1 2 5 (by decide) (by decide) with h545 | h545
          · rcases m.htr 1 3 4 (by decide) (by decide) with h546 | h546
            · linarith only [h1, h546, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h548 | h548
              · rcases m.htr 1 4 5 (by decide) (by decide) with h549 | h549
                · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
                  · linarith only [h1, h543, h550, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h552 | h552
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h553 | h553
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h554 | h554
                        · rcases h0bigk with h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [hlam, p555_0]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h0, h544, h550, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p555_1]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            rcases p555_3 (m.d 0 1) (by simp) with h558 | h558
                            · rcases p555_3 (m.d 0 2) (by simp) with h559 | h559
                              · linarith only [h0, h559, hlam]
                              · linarith only [h4, h559, hlam]
                            · linarith only [h1, h558, hlam]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            rcases p555_3 (m.d 0 1) (by simp) with h563 | h563
                            · rcases p555_3 (m.d 0 2) (by simp) with h564 | h564
                              · linarith only [h0, h564, hlam]
                              · linarith only [h5, h564, hlam]
                            · linarith only [h2, h563, hlam]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            rcases p555_3 (m.d 0 1) (by simp) with h568 | h568
                            · rcases p555_3 (m.d 0 2) (by simp) with h569 | h569
                              · linarith only [h0, h569, hlam]
                              · linarith only [h569, h6, hlam]
                            · linarith only [h3, h568, hlam]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h0, hlam, p555_0]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [hlam, p555_0]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            rcases p555_3 (m.d 0 1) (by simp) with h575 | h575
                            · rcases p555_3 (m.d 0 2) (by simp) with h576 | h576
                              · rcases p555_3 (m.d 0 3) (by simp) with h577 | h577
                                · linarith only [h4, h577, hlam]
                                · rcases p555_3 (m.d 0 4) (by simp) with h579 | h579
                                  · linarith only [h5, h579, hlam]
                                  · linarith only [h579, h7, hlam]
                              · linarith only [h4, h576, hlam]
                            · linarith only [h1, h575, hlam]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            rcases p555_3 (m.d 0 1) (by simp) with h584 | h584
                            · rcases p555_3 (m.d 0 2) (by simp) with h585 | h585
                              · rcases p555_3 (m.d 0 3) (by simp) with h586 | h586
                                · linarith only [h4, h586, hlam]
                                · rcases p555_3 (m.d 0 4) (by simp) with h588 | h588
                                  · linarith only [h5, h588, hlam]
                                  · rcases p555_3 (m.d 0 5) (by simp) with h590 | h590
                                    · linarith only [h590, h6, hlam]
                                    · rcases h0emin with h592 | h592 | h592 | h592 | h592
                                      · rcases h2bigk with h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h544, h550, h552, h554, hc02, hc45, hlam, hphi, ht0b, ht5b, p593_1]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          rcases p593_3 (m.d 0 2) (by simp) with h596 | h596
                                          · rcases p593_3 (m.d 1 2) (by simp) with h597 | h597
                                            · linarith only [h0, h597, hlam]
                                            · linarith only [h543, h597, hlam]
                                          · linarith only [h596, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          rcases p593_3 (m.d 0 2) (by simp) with h601 | h601
                                          · rcases p593_3 (m.d 1 2) (by simp) with h602 | h602
                                            · linarith only [h0, h602, hlam]
                                            · linarith only [h544, h602, hlam]
                                          · linarith only [h601, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          rcases p593_3 (m.d 0 2) (by simp) with h606 | h606
                                          · rcases p593_3 (m.d 1 2) (by simp) with h607 | h607
                                            · linarith only [h0, h607, hlam]
                                            · linarith only [h545, h607, hlam]
                                          · linarith only [h606, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h0, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h0, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p593_1]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h0, h550, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p593_1]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          rcases p593_3 (m.d 0 2) (by simp) with h615 | h615
                                          · rcases p593_3 (m.d 1 2) (by simp) with h616 | h616
                                            · rcases p593_3 (m.d 2 3) (by simp) with h617 | h617
                                              · linarith only [h543, h617, hlam]
                                              · linarith only [h552, h617, hlam]
                                            · linarith only [h616, hlam, p593_0]
                                          · linarith only [h6, h615, hlam]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h4, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h543, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h550, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h1, h543, h7, hc02, hc25, hlam, hphi, ht0b, ht5b, p555_1, p593_1]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h5, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h544, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p555_1, p593_1]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h0, h2, h544, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p555_1, p593_1]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h6, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h545, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h552, hlam, p593_1]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [h553, hlam, p593_0]
                                        · have p593_0 := h593c.1
                                          have p593_1 := h593c.2.1
                                          have p593_2 := h593c.2.2.1
                                          have p593_3 := h593c.2.2.2
                                          linarith only [hlam, p593_0]
                                      · rcases h2bigk with h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h0, h543, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p637_1]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          rcases p637_3 (m.d 0 2) (by simp) with h640 | h640
                                          · rcases p637_3 (m.d 1 2) (by simp) with h641 | h641
                                            · linarith only [h0, h641, hlam]
                                            · linarith only [h543, h641, hlam]
                                          · linarith only [h640, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          rcases p637_3 (m.d 0 2) (by simp) with h645 | h645
                                          · rcases p637_3 (m.d 1 2) (by simp) with h646 | h646
                                            · linarith only [h0, h646, hlam]
                                            · linarith only [h544, h646, hlam]
                                          · linarith only [h645, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          rcases p637_3 (m.d 0 2) (by simp) with h650 | h650
                                          · rcases p637_3 (m.d 1 2) (by simp) with h651 | h651
                                            · linarith only [h0, h651, hlam]
                                            · linarith only [h545, h651, hlam]
                                          · linarith only [h650, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h0, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h0, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p637_1]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h0, h550, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p637_1]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          rcases p637_3 (m.d 0 2) (by simp) with h659 | h659
                                          · rcases p637_3 (m.d 1 2) (by simp) with h660 | h660
                                            · rcases p637_3 (m.d 2 3) (by simp) with h661 | h661
                                              · linarith only [h543, h661, hlam]
                                              · linarith only [h552, h661, hlam]
                                            · linarith only [h660, hlam, p637_0]
                                          · linarith only [h6, h659, hlam]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h4, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h543, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h550, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h4, h7, hc02, hc25, hlam, hphi, ht0b, ht5b, p555_1, p637_1]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h5, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h544, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p555_1, p637_1]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h0, h2, h544, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p555_1, p637_1]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h6, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h545, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h552, hlam, p637_1]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [h553, hlam, p637_0]
                                        · have p637_0 := h637c.1
                                          have p637_1 := h637c.2.1
                                          have p637_2 := h637c.2.2.1
                                          have p637_3 := h637c.2.2.2
                                          linarith only [hlam, p637_0]
                                      · linarith only [h0, h592, h7, hc01, hlam, p555_1]
                                      · linarith only [h0, h592, hc01, hlam, p555_1]
                                      · linarith only [h592, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                              · linarith only [h5, h585, hlam]
                            · linarith only [h2, h584, hlam]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            rcases p555_3 (m.d 0 1) (by simp) with h686 | h686
                            · rcases p555_3 (m.d 0 2) (by simp) with h687 | h687
                              · rcases p555_3 (m.d 0 3) (by simp) with h688 | h688
                                · linarith only [h4, h688, hlam]
                                · linarith only [h541, h688, hlam]
                              · linarith only [h6, h687, hlam]
                            · linarith only [h3, h686, hlam]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h1, hlam, p555_1]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h4, hlam, p555_1]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [hlam, p555_0]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h7, hlam, p555_1]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            rcases p555_3 (m.d 0 1) (by simp) with h697 | h697
                            · rcases p555_3 (m.d 0 2) (by simp) with h698 | h698
                              · rcases p555_3 (m.d 0 3) (by simp) with h699 | h699
                                · rcases p555_3 (m.d 0 4) (by simp) with h700 | h700
                                  · rcases p555_3 (m.d 0 5) (by simp) with h701 | h701
                                    · linarith only [h541, h701, hlam]
                                    · rcases h0emin with h703 | h703 | h703 | h703 | h703
                                      · rcases h2bigk with h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h0, h544, h550, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p704_1]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          rcases p704_3 (m.d 0 2) (by simp) with h707 | h707
                                          · rcases p704_3 (m.d 1 2) (by simp) with h708 | h708
                                            · linarith only [h0, h708, hlam]
                                            · linarith only [h543, h708, hlam]
                                          · linarith only [h707, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          rcases p704_3 (m.d 0 2) (by simp) with h712 | h712
                                          · rcases p704_3 (m.d 1 2) (by simp) with h713 | h713
                                            · linarith only [h0, h713, hlam]
                                            · linarith only [h544, h713, hlam]
                                          · linarith only [h712, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          rcases p704_3 (m.d 0 2) (by simp) with h717 | h717
                                          · rcases p704_3 (m.d 1 2) (by simp) with h718 | h718
                                            · linarith only [h0, h718, hlam]
                                            · linarith only [h545, h718, hlam]
                                          · linarith only [h717, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h0, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h0, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p704_1]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h0, h550, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p704_1]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          rcases p704_3 (m.d 0 2) (by simp) with h726 | h726
                                          · rcases p704_3 (m.d 1 2) (by simp) with h727 | h727
                                            · rcases p704_3 (m.d 2 3) (by simp) with h728 | h728
                                              · linarith only [h543, h728, hlam]
                                              · linarith only [h552, h728, hlam]
                                            · linarith only [h727, hlam, p704_0]
                                          · linarith only [h6, h726, hlam]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h4, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h543, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h550, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h0, h543, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p704_1]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h5, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h544, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h0, h544, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p704_1]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h0, h544, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p704_1]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h6, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h545, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h552, hlam, p704_1]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [h553, hlam, p704_0]
                                        · have p704_0 := h704c.1
                                          have p704_1 := h704c.2.1
                                          have p704_2 := h704c.2.2.1
                                          have p704_3 := h704c.2.2.2
                                          linarith only [hlam, p704_0]
                                      · rcases h2bigk with h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h0, h543, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p748_1]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          rcases p748_3 (m.d 0 2) (by simp) with h751 | h751
                                          · rcases p748_3 (m.d 1 2) (by simp) with h752 | h752
                                            · linarith only [h0, h752, hlam]
                                            · linarith only [h543, h752, hlam]
                                          · linarith only [h751, hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          rcases p748_3 (m.d 0 2) (by simp) with h756 | h756
                                          · rcases p748_3 (m.d 1 2) (by simp) with h757 | h757
                                            · linarith only [h0, h757, hlam]
                                            · linarith only [h544, h757, hlam]
                                          · linarith only [h756, hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          rcases p748_3 (m.d 0 2) (by simp) with h761 | h761
                                          · rcases p748_3 (m.d 1 2) (by simp) with h762 | h762
                                            · linarith only [h0, h762, hlam]
                                            · linarith only [h545, h762, hlam]
                                          · linarith only [h761, hlam, p748_0]
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
                                          linarith only [h0, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p748_1]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h0, h550, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p748_1]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          rcases p748_3 (m.d 0 2) (by simp) with h770 | h770
                                          · rcases p748_3 (m.d 1 2) (by simp) with h771 | h771
                                            · rcases p748_3 (m.d 2 3) (by simp) with h772 | h772
                                              · linarith only [h543, h772, hlam]
                                              · linarith only [h552, h772, hlam]
                                            · linarith only [h771, hlam, p748_0]
                                          · linarith only [h6, h770, hlam]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h4, hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h543, hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h550, hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h0, h543, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p748_1]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h5, hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h544, hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h0, h3, h544, h545, h552, h554, h7, hc01, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p555_1, p748_1]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h0, h544, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p748_1]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h6, hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h545, hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h552, hlam, p748_1]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [h553, hlam, p748_0]
                                        · have p748_0 := h748c.1
                                          have p748_1 := h748c.2.1
                                          have p748_2 := h748c.2.2.1
                                          have p748_3 := h748c.2.2.2
                                          linarith only [hlam, p748_0]
                                      · linarith only [h7, h703, hc34, hlam, ht01, ht12, ht23]
                                      · rcases h2bigk with h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h0, h543, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p793_1]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          rcases p793_3 (m.d 0 2) (by simp) with h796 | h796
                                          · rcases p793_3 (m.d 1 2) (by simp) with h797 | h797
                                            · linarith only [h0, h797, hlam]
                                            · linarith only [h543, h797, hlam]
                                          · linarith only [h796, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          rcases p793_3 (m.d 0 2) (by simp) with h801 | h801
                                          · rcases p793_3 (m.d 1 2) (by simp) with h802 | h802
                                            · linarith only [h0, h802, hlam]
                                            · linarith only [h544, h802, hlam]
                                          · linarith only [h801, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          rcases p793_3 (m.d 0 2) (by simp) with h806 | h806
                                          · rcases p793_3 (m.d 1 2) (by simp) with h807 | h807
                                            · linarith only [h0, h807, hlam]
                                            · linarith only [h545, h807, hlam]
                                          · linarith only [h806, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h0, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h0, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p793_1]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h0, h550, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p793_1]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          rcases p793_3 (m.d 0 2) (by simp) with h815 | h815
                                          · rcases p793_3 (m.d 1 2) (by simp) with h816 | h816
                                            · rcases p793_3 (m.d 2 3) (by simp) with h817 | h817
                                              · linarith only [h543, h817, hlam]
                                              · linarith only [h552, h817, hlam]
                                            · linarith only [h816, hlam, p793_0]
                                          · linarith only [h6, h815, hlam]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h4, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h543, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h550, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h0, h543, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p793_1]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h5, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h544, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h0, h3, h544, h545, h552, h554, h7, hc01, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p555_1, p793_1]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h0, h544, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p793_1]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h6, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h545, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h552, hlam, p793_1]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [h553, hlam, p793_0]
                                        · have p793_0 := h793c.1
                                          have p793_1 := h793c.2.1
                                          have p793_2 := h793c.2.2.1
                                          have p793_3 := h793c.2.2.2
                                          linarith only [hlam, p793_0]
                                      · linarith only [h7, h703, hc34, hlam, ht01, ht12, ht23, p555_1]
                                  · linarith only [h542, h700, hlam]
                                · linarith only [h541, h699, hlam]
                              · linarith only [h6, h698, hlam]
                            · linarith only [h3, h697, hlam]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h2, hlam, p555_0]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h5, hlam, p555_0]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            rcases p555_3 (m.d 0 1) (by simp) with h844 | h844
                            · rcases p555_3 (m.d 0 2) (by simp) with h845 | h845
                              · rcases p555_3 (m.d 0 3) (by simp) with h846 | h846
                                · linarith only [h7, h846, hlam]
                                · rcases p555_3 (m.d 0 4) (by simp) with h848 | h848
                                  · rcases p555_3 (m.d 0 5) (by simp) with h849 | h849
                                    · linarith only [h542, h849, hlam]
                                    · rcases h0emin with h851 | h851 | h851 | h851 | h851
                                      · rcases h2bigk with h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h0, h543, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p852_1]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          rcases p852_3 (m.d 0 2) (by simp) with h855 | h855
                                          · rcases p852_3 (m.d 1 2) (by simp) with h856 | h856
                                            · linarith only [h0, h856, hlam]
                                            · linarith only [h543, h856, hlam]
                                          · linarith only [h855, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          rcases p852_3 (m.d 0 2) (by simp) with h860 | h860
                                          · rcases p852_3 (m.d 1 2) (by simp) with h861 | h861
                                            · linarith only [h0, h861, hlam]
                                            · linarith only [h544, h861, hlam]
                                          · linarith only [h860, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          rcases p852_3 (m.d 0 2) (by simp) with h865 | h865
                                          · rcases p852_3 (m.d 1 2) (by simp) with h866 | h866
                                            · linarith only [h0, h866, hlam]
                                            · linarith only [h545, h866, hlam]
                                          · linarith only [h865, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h0, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h0, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p852_1]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h0, h550, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p852_1]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          rcases p852_3 (m.d 0 2) (by simp) with h874 | h874
                                          · rcases p852_3 (m.d 1 2) (by simp) with h875 | h875
                                            · rcases p852_3 (m.d 2 3) (by simp) with h876 | h876
                                              · linarith only [h543, h876, hlam]
                                              · linarith only [h552, h876, hlam]
                                            · linarith only [h875, hlam, p852_0]
                                          · linarith only [h6, h874, hlam]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h4, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h543, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h550, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h1, h5, h543, hc02, hc25, hlam, hphi, ht0b, ht5b, p555_1, p852_1]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h5, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h544, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h0, h544, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p852_1]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h0, h544, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p852_1]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h6, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h545, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h552, hlam, p852_1]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [h553, hlam, p852_0]
                                        · have p852_0 := h852c.1
                                          have p852_1 := h852c.2.1
                                          have p852_2 := h852c.2.2.1
                                          have p852_3 := h852c.2.2.2
                                          linarith only [hlam, p852_0]
                                      · rcases h2bigk with h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h0, h543, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p896_1]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          rcases p896_3 (m.d 0 2) (by simp) with h899 | h899
                                          · rcases p896_3 (m.d 1 2) (by simp) with h900 | h900
                                            · linarith only [h0, h900, hlam]
                                            · linarith only [h543, h900, hlam]
                                          · linarith only [h899, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          rcases p896_3 (m.d 0 2) (by simp) with h904 | h904
                                          · rcases p896_3 (m.d 1 2) (by simp) with h905 | h905
                                            · linarith only [h0, h905, hlam]
                                            · linarith only [h544, h905, hlam]
                                          · linarith only [h904, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          rcases p896_3 (m.d 0 2) (by simp) with h909 | h909
                                          · rcases p896_3 (m.d 1 2) (by simp) with h910 | h910
                                            · linarith only [h0, h910, hlam]
                                            · linarith only [h545, h910, hlam]
                                          · linarith only [h909, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h0, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h0, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p896_1]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h0, h550, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p896_1]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          rcases p896_3 (m.d 0 2) (by simp) with h918 | h918
                                          · rcases p896_3 (m.d 1 2) (by simp) with h919 | h919
                                            · rcases p896_3 (m.d 2 3) (by simp) with h920 | h920
                                              · linarith only [h543, h920, hlam]
                                              · linarith only [h552, h920, hlam]
                                            · linarith only [h919, hlam, p896_0]
                                          · linarith only [h6, h918, hlam]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h4, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h543, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h550, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h1, h543, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p555_1, p896_1]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h5, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h544, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h5, h552, hc02, hc35, hlam, hphi, ht0b, ht5b, p896_1]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h0, h544, h552, hc01, hc35, hlam, hphi, ht0b, ht5b, p896_1]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h6, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h545, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h552, hlam, p896_1]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [h553, hlam, p896_0]
                                        · have p896_0 := h896c.1
                                          have p896_1 := h896c.2.1
                                          have p896_2 := h896c.2.2.1
                                          have p896_3 := h896c.2.2.2
                                          linarith only [hlam, p896_0]
                                      · linarith only [h7, h851, hc34, hlam, ht01, ht12, ht23, p555_1]
                                      · rcases h2bigk with h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h0, h543, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p941_1]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          rcases p941_3 (m.d 0 2) (by simp) with h944 | h944
                                          · rcases p941_3 (m.d 1 2) (by simp) with h945 | h945
                                            · linarith only [h0, h945, hlam]
                                            · linarith only [h543, h945, hlam]
                                          · linarith only [h944, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          rcases p941_3 (m.d 0 2) (by simp) with h949 | h949
                                          · rcases p941_3 (m.d 1 2) (by simp) with h950 | h950
                                            · linarith only [h0, h950, hlam]
                                            · linarith only [h544, h950, hlam]
                                          · linarith only [h949, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          rcases p941_3 (m.d 0 2) (by simp) with h954 | h954
                                          · rcases p941_3 (m.d 1 2) (by simp) with h955 | h955
                                            · linarith only [h0, h955, hlam]
                                            · linarith only [h545, h955, hlam]
                                          · linarith only [h954, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h0, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h0, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p941_1]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h0, h550, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p941_1]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          rcases p941_3 (m.d 0 2) (by simp) with h963 | h963
                                          · rcases p941_3 (m.d 1 2) (by simp) with h964 | h964
                                            · rcases p941_3 (m.d 2 3) (by simp) with h965 | h965
                                              · linarith only [h543, h965, hlam]
                                              · linarith only [h552, h965, hlam]
                                            · linarith only [h964, hlam, p941_0]
                                          · linarith only [h6, h963, hlam]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h4, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h543, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h550, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h1, h5, h543, hc02, hc25, hlam, hphi, ht0b, ht5b, p555_1, p941_1]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h5, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h544, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h0, h544, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p941_1]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h0, h544, h552, h554, hc01, hc45, hlam, hphi, ht0b, ht5b, p941_1]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h6, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h545, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h552, hlam, p941_1]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [h553, hlam, p941_0]
                                        · have p941_0 := h941c.1
                                          have p941_1 := h941c.2.1
                                          have p941_2 := h941c.2.2.1
                                          have p941_3 := h941c.2.2.2
                                          linarith only [hlam, p941_0]
                                      · linarith only [h1, h543, h552, h554, h7, h851, hc34, hc45, hlam, hphi, ht01, ht12, ht23, p555_1, u5elo0]
                                  · linarith only [h7, h848, hlam]
                              · linarith only [h4, h845, hlam]
                            · linarith only [h1, h844, hlam]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [hlam, p555_0]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            rcases p555_3 (m.d 0 1) (by simp) with h990 | h990
                            · rcases p555_3 (m.d 0 2) (by simp) with h991 | h991
                              · rcases p555_3 (m.d 0 3) (by simp) with h992 | h992
                                · linarith only [h7, h992, hlam]
                                · linarith only [h541, h992, hlam]
                              · linarith only [h6, h991, hlam]
                            · linarith only [h3, h990, hlam]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h3, hlam, p555_0]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h6, hlam, p555_1]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h541, hlam, p555_0]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [h542, hlam, p555_1]
                          · have p555_0 := h555c.1
                            have p555_1 := h555c.2.1
                            have p555_2 := h555c.2.2.1
                            have p555_3 := h555c.2.2.2
                            linarith only [hlam, p555_0]
                        · linarith only [h554, h7, hc04, hlam, hphi, ht45, u5elo4]
                      · linarith only [h549, h553, hc24, hlam, hphi, ht45, u5elo1]
                    · linarith only [h1, h548, h552, h7, hc23, hc34, hlam, hphi]
                · linarith only [h542, h546, h549, hc13, hlam, hphi, ht34, ht45, u5elo0]
              · linarith only [h543, h548, hc23, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h545, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1008 | h1008
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1009 | h1009
            · linarith only [h1, h1009, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1011 | h1011
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1012 | h1012
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1013 | h1013
                  · linarith only [h1013, h5, h543, h544, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1015 | h1015
                    · linarith only [h0, h1015, h5, h543, h544, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1015, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1012, h544, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h1011, hc13, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h1008, h543, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1021 | h1021
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1022 | h1022
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1023 | h1023
            · linarith only [h1022, h1023, h4, h543, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1021, h1023, h543, hlam]
          · linarith only [h1021, h1022, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1027 | h1027
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1028 | h1028
            · linarith only [h1027, h1028, h4, h543, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1030 | h1030
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1031 | h1031
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1032 | h1032
                  · linarith only [h1032, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1034 | h1034
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1035 | h1035
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1036 | h1036
                        · rcases h0bigk with h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h1027, h1032, h1034, h1036, h5, h543, hc01, hc45, hlam, hphi, ht0b, ht5b, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h1027, h1034, h1036, h4, h543, hc01, hc45, hlam, hphi, ht0b, ht5b, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h1027, h1034, h1036, h4, h543, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            rcases p1037_3 (m.d 0 1) (by simp) with h1042 | h1042
                            · rcases p1037_3 (m.d 0 2) (by simp) with h1043 | h1043
                              · linarith only [h0, h1043, hlam]
                              · linarith only [h1043, h6, hlam]
                            · linarith only [h1042, h3, hlam]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h0, hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h1027, h1034, h1036, h4, h543, hc02, hc45, hlam, hphi, ht0b, ht5b, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h0, h1027, h1034, h1036, h4, h543, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            rcases p1037_3 (m.d 0 1) (by simp) with h1051 | h1051
                            · rcases p1037_3 (m.d 0 2) (by simp) with h1052 | h1052
                              · rcases p1037_3 (m.d 0 3) (by simp) with h1053 | h1053
                                · linarith only [h1053, h4, hlam]
                                · linarith only [h1053, h541, hlam]
                              · linarith only [h1052, h6, hlam]
                            · linarith only [h1051, h3, hlam]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h1, hlam, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h4, hlam, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h7, hlam, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            rcases p1037_3 (m.d 0 1) (by simp) with h1062 | h1062
                            · rcases p1037_3 (m.d 0 2) (by simp) with h1063 | h1063
                              · rcases p1037_3 (m.d 0 3) (by simp) with h1064 | h1064
                                · rcases p1037_3 (m.d 0 4) (by simp) with h1065 | h1065
                                  · rcases p1037_3 (m.d 0 5) (by simp) with h1066 | h1066
                                    · linarith only [h1066, h541, hlam]
                                    · rcases h0emin with h1068 | h1068 | h1068 | h1068 | h1068
                                      · rcases h2bigk with h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          rcases p1069_3 (m.d 0 2) (by simp) with h1071 | h1071
                                          · rcases p1069_3 (m.d 1 2) (by simp) with h1072 | h1072
                                            · linarith only [h0, h1072, hlam]
                                            · rcases p1069_3 (m.d 2 3) (by simp) with h1074 | h1074
                                              · linarith only [h1074, h4, hlam]
                                              · linarith only [h1074, h543, hlam]
                                          · linarith only [h0, h1071, hlam]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h0, h1027, h1034, h1036, h543, hc01, hc45, hlam, hphi, ht0b, ht5b, p1069_1]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h0, h1027, h1032, h1034, h1036, h543, hc01, hc45, hlam, hphi, ht0b, ht5b, p1069_1]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h1027, h4, h543, hlam, p1069_2]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h0, hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h543, hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h1021, hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h1034, h1036, h4, h543, hc02, hc45, hlam, hphi, ht0b, ht5b, p1069_1]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h4, hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p1069_1]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h1032, hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          rcases p1069_3 (m.d 0 2) (by simp) with h1090 | h1090
                                          · rcases p1069_3 (m.d 1 2) (by simp) with h1091 | h1091
                                            · linarith only [h1091, h543, hlam]
                                            · linarith only [h1027, h1091, hlam]
                                          · linarith only [h1090, h6, hlam]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h5, hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h0, h1027, h1034, h1036, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1069_1]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h0, h1027, h1034, h1036, h5, h543, hc01, hc45, hlam, hphi, ht0b, ht5b, p1069_1]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          rcases p1069_3 (m.d 0 2) (by simp) with h1099 | h1099
                                          · rcases p1069_3 (m.d 1 2) (by simp) with h1100 | h1100
                                            · linarith only [h1021, h1100, hlam]
                                            · linarith only [h1027, h1100, hlam]
                                          · linarith only [h1099, h6, hlam]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h6, hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h1027, hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h1034, hlam, p1069_1]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [h1035, hlam, p1069_0]
                                        · have p1069_0 := h1069c.1
                                          have p1069_1 := h1069c.2.1
                                          have p1069_2 := h1069c.2.2.1
                                          have p1069_3 := h1069c.2.2.2
                                          linarith only [hlam, p1069_0]
                                      · rcases h2bigk with h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          rcases p1109_3 (m.d 0 2) (by simp) with h1111 | h1111
                                          · rcases p1109_3 (m.d 1 2) (by simp) with h1112 | h1112
                                            · linarith only [h0, h1112, hlam]
                                            · rcases p1109_3 (m.d 2 3) (by simp) with h1114 | h1114
                                              · linarith only [h1114, h4, hlam]
                                              · linarith only [h1114, h543, hlam]
                                          · linarith only [h0, h1111, hlam]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h0, h1027, h1034, h1036, h543, hc01, hc45, hlam, hphi, ht0b, ht5b, p1109_1]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h0, h1021, h1027, h1034, h1036, hc01, hc45, hlam, hphi, ht0b, ht5b, p1109_1]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h1027, h4, h543, hlam, p1109_2]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h0, hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h543, hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h1021, hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h1034, h1036, h4, h543, hc02, hc45, hlam, hphi, ht0b, ht5b, p1109_1]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h4, hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p1109_1]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h1032, hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          rcases p1109_3 (m.d 0 2) (by simp) with h1130 | h1130
                                          · rcases p1109_3 (m.d 1 2) (by simp) with h1131 | h1131
                                            · linarith only [h1131, h543, hlam]
                                            · linarith only [h1027, h1131, hlam]
                                          · linarith only [h1130, h6, hlam]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h5, hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h0, h1027, h1034, h1036, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1109_1]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h1027, h1034, h1036, h5, h543, hc04, hc45, hlam, hphi, ht0b, ht5b, p1109_1]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          rcases p1109_3 (m.d 0 2) (by simp) with h1139 | h1139
                                          · rcases p1109_3 (m.d 1 2) (by simp) with h1140 | h1140
                                            · linarith only [h1021, h1140, hlam]
                                            · linarith only [h1027, h1140, hlam]
                                          · linarith only [h1139, h6, hlam]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h6, hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h1027, hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h1034, hlam, p1109_1]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [h1035, hlam, p1109_0]
                                        · have p1109_0 := h1109c.1
                                          have p1109_1 := h1109c.2.1
                                          have p1109_2 := h1109c.2.2.1
                                          have p1109_3 := h1109c.2.2.2
                                          linarith only [hlam, p1109_0]
                                      · linarith only [h1068, h7, hc34, hlam, ht01, ht12, ht23]
                                      · rcases h2bigk with h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          rcases p1150_3 (m.d 0 2) (by simp) with h1152 | h1152
                                          · rcases p1150_3 (m.d 1 2) (by simp) with h1153 | h1153
                                            · linarith only [h0, h1153, hlam]
                                            · rcases p1150_3 (m.d 2 3) (by simp) with h1155 | h1155
                                              · linarith only [h1155, h4, hlam]
                                              · linarith only [h1155, h543, hlam]
                                          · linarith only [h0, h1152, hlam]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h0, h1027, h1034, h1036, h543, hc01, hc45, hlam, hphi, ht0b, ht5b, p1150_1]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h0, h1021, h1027, h1034, h1036, hc01, hc45, hlam, hphi, ht0b, ht5b, p1150_1]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h1027, h4, h543, hlam, p1150_2]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h0, hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h543, hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h1021, hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h1034, h1036, h4, h543, hc02, hc45, hlam, hphi, ht0b, ht5b, p1150_1]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h4, hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p1150_1]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h1032, hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          rcases p1150_3 (m.d 0 2) (by simp) with h1171 | h1171
                                          · rcases p1150_3 (m.d 1 2) (by simp) with h1172 | h1172
                                            · linarith only [h1172, h543, hlam]
                                            · linarith only [h1027, h1172, hlam]
                                          · linarith only [h1171, h6, hlam]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h5, hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h0, h1027, h1034, h1036, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1150_1]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h0, h1027, h1034, h1036, h5, h543, hc01, hc45, hlam, hphi, ht0b, ht5b, p1150_1]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          rcases p1150_3 (m.d 0 2) (by simp) with h1180 | h1180
                                          · rcases p1150_3 (m.d 1 2) (by simp) with h1181 | h1181
                                            · linarith only [h1021, h1181, hlam]
                                            · linarith only [h1027, h1181, hlam]
                                          · linarith only [h1180, h6, hlam]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h6, hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h1027, hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h1034, hlam, p1150_1]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [h1035, hlam, p1150_0]
                                        · have p1150_0 := h1150c.1
                                          have p1150_1 := h1150c.2.1
                                          have p1150_2 := h1150c.2.2.1
                                          have p1150_3 := h1150c.2.2.2
                                          linarith only [hlam, p1150_0]
                                      · linarith only [h1068, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h1065, h542, hlam]
                                · linarith only [h1064, h541, hlam]
                              · linarith only [h1063, h6, hlam]
                            · linarith only [h1062, h3, hlam]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h2, hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h5, hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h1027, h1034, h1036, h4, h543, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            rcases p1037_3 (m.d 0 1) (by simp) with h1199 | h1199
                            · rcases p1037_3 (m.d 0 2) (by simp) with h1200 | h1200
                              · rcases p1037_3 (m.d 0 3) (by simp) with h1201 | h1201
                                · linarith only [h1201, h7, hlam]
                                · linarith only [h1201, h541, hlam]
                              · linarith only [h1200, h6, hlam]
                            · linarith only [h1199, h3, hlam]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h3, hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h6, hlam, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h541, hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h542, hlam, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [hlam, p1037_0]
                        · linarith only [h1036, h7, hc04, hlam, hphi, ht45, u5elo4]
                      · linarith only [h1035, hc24, hlam, hphi, ht45, u5elo4]
                    · linarith only [h1034, h543, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h1031, hc14, hlam, hphi, ht45, u5elo4]
              · linarith only [h1030, hc13, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h1027, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h542, hc04, hlam, hphi, ht45, u5elo4]
  · linarith only [h541, hc03, hlam, hphi, ht34, ht45, u5elo3]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6

end R2N4
