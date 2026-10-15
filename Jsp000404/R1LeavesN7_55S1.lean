import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_55S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h560 | h560
  · rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
    · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
      · rcases m.htr 1 2 4 (by decide) (by decide) with h563 | h563
        · rcases m.htr 1 2 5 (by decide) (by decide) with h564 | h564
          · linarith only [h4, h564, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h566 | h566
            · rcases m.htr 1 3 5 (by decide) (by decide) with h567 | h567
              · linarith only [h562, h564, h567, hlam]
              · linarith only [h1, h560, h566, h567, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h570 | h570
              · linarith only [h562, h564, h570, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h572 | h572
                · linarith only [h563, h564, h572, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h574 | h574
                  · linarith only [h562, h566, h574, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
                    · linarith only [h1, h562, h563, h564, h570, h576, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h0, h1, h4, h560, h563, h574, h576, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h579 | h579
          · linarith only [h0, h4, h579, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h581 | h581
            · linarith only [h562, h563, h581, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h583 | h583
              · linarith only [h562, h579, h583, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h585 | h585
                · rcases m.htr 2 3 4 (by decide) (by decide) with h586 | h586
                  · linarith only [h0, h4, h562, h581, h586, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h588 | h588
                    · linarith only [h562, h579, h583, h588, hlam]
                    · linarith only [h0, h1, h4, h560, h562, h588, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h2, h561, h562, h563, h585, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h592 | h592
        · rcases m.htr 1 2 5 (by decide) (by decide) with h593 | h593
          · linarith only [h0, h4, h593, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h595 | h595
            · rcases m.htr 1 3 5 (by decide) (by decide) with h596 | h596
              · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
                · linarith only [h592, h593, h597, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h599 | h599
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h600 | h600
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h601 | h601
                      · linarith only [h592, h597, h601, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h4, h561, h601, hlam]
                    · linarith only [h1, h596, h600, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1, h562, h595, h599, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1, h560, h562, h592, h596, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h562, h592, h595, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h608 | h608
          · linarith only [h0, h4, h608, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h610 | h610
            · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
              · rcases m.htr 1 4 5 (by decide) (by decide) with h612 | h612
                · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h614 | h614
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h615 | h615
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h616 | h616
                        · linarith only [h1, h610, h616, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h2, h612, h616, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h610, h612, h615, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h3, h4, h562, h611, h614, hc12, hlam, hphi, u2elo4]
                  · linarith only [h562, h610, h613, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h622 | h622
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h623 | h623
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h624 | h624
                      · linarith only [h592, h612, h624, hc12, hlam, hphi, u2elo3]
                      · linarith only [h2, h561, h592, h624, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1, h611, h623, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h2, h561, h562, h610, h612, h622, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1, h560, h610, h611, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h630 | h630
              · rcases m.htr 1 4 5 (by decide) (by decide) with h631 | h631
                · rcases m.htr 2 3 4 (by decide) (by decide) with h632 | h632
                  · linarith only [h610, h630, h632, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h634 | h634
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h635 | h635
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h636 | h636
                        · rcases h5bigk with h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [hlam, p637_0]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h4, h608, h632, h634, hc12, hlam, hphi, p637_1, u2elo3]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h4, hlam, p637_0]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h4, h632, h634, h636, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p637_1, u2elo3]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h4, h632, h634, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p637_1, u2elo3]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h3, hlam, p637_0]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [hlam, p637_0]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h608, hlam, p637_0]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h636, hc45, hlam, hphi, ht01, ht0b, ht5b, p637_1, u1elo4]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h630, hc45, hlam, hphi, ht01, ht0b, ht5b, p637_1, u1elo2]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h632, h634, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p637_1, u2elo3]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h632, h634, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p637_1, u2elo3]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [hlam, p637_0]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h632, h634, h636, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p637_1, u2elo3]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h632, h634, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p637_1, u2elo3]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h560, hlam, p637_1]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h630, hlam, p637_1]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h634, hlam, p637_0]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [hlam, p637_0]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h1, h560, hc45, hlam, hphi, ht01, ht0b, ht5b, p637_1, u1elo0]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h561, hlam, p637_1]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h631, hlam, p637_1]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h635, hlam, p637_1]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [h636, hlam, p637_1]
                          · have p637_0 := h637c.1
                            have p637_1 := h637c.2.1
                            have p637_2 := h637c.2.2.1
                            have p637_3 := h637c.2.2.2
                            linarith only [hlam, p637_0]
                        · linarith only [h3, h561, h610, h630, h636, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h2, h4, h631, h632, h634, h635, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h562, h630, h634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h2, h561, h610, h630, h631, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h667 | h667
                · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                  · linarith only [h562, h610, h668, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h670 | h670
                    · linarith only [h562, h630, h670, hc12, hlam, hphi, u2elo2]
                    · linarith only [h1, h560, h562, h670, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h673 | h673
                  · linarith only [h562, h610, h673, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h675 | h675
                    · linarith only [h562, h630, h673, h675, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h560, h562, h675, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h678 | h678
      · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
        · rcases m.htr 1 2 5 (by decide) (by decide) with h680 | h680
          · linarith only [h0, h4, h680, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h682 | h682
            · rcases m.htr 1 3 5 (by decide) (by decide) with h683 | h683
              · linarith only [h678, h680, h683, hlam]
              · linarith only [h1, h560, h682, h683, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h686 | h686
              · linarith only [h679, h680, h682, h686, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h688 | h688
                · linarith only [h2, h561, h688, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h690 | h690
                  · linarith only [h0, h4, h678, h690, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h692 | h692
                    · linarith only [h679, h680, h686, h690, h692, hlam]
                    · linarith only [h0, h1, h4, h560, h679, h690, h692, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h695 | h695
          · linarith only [h0, h4, h695, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h697 | h697
            · linarith only [h678, h679, h697, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h699 | h699
              · linarith only [h678, h695, h699, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h701 | h701
                · linarith only [h2, h561, h701, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h703 | h703
                  · linarith only [h678, h697, h703, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h705 | h705
                    · linarith only [h678, h679, h699, h701, h705, hlam]
                    · linarith only [h4, h560, h705, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h708 | h708
        · rcases m.htr 1 2 5 (by decide) (by decide) with h709 | h709
          · linarith only [h0, h4, h709, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h711 | h711
            · rcases m.htr 1 3 5 (by decide) (by decide) with h712 | h712
              · rcases m.htr 1 4 5 (by decide) (by decide) with h713 | h713
                · linarith only [h561, h678, h708, h713, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h715 | h715
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h716 | h716
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h717 | h717
                      · linarith only [h2, h561, h708, h717, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h719 | h719
                        · linarith only [h0, h4, h708, h715, h717, h719, hlam]
                        · rcases h5bigk with h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h708, h709, h715, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h4, hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h4, h716, h719, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p721_1, u2elo2]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h561, hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h3, hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h709, hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h712, h719, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p721_1, u1elo2]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h713, hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h716, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p721_1, u2elo2]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h716, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p721_1, u2elo2]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h716, h719, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p721_1, u2elo2]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h717, hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h560, hlam, p721_1]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h712, hlam, p721_1]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h716, hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h719, hlam, p721_0]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h0, h4, h708, h715, hc34, hc45, hlam, hphi, p721_1]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h708, h709, h715, hc34, hc45, hlam, hphi, p721_1]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h0, h4, h708, h715, hc34, hc45, hlam, hphi, p721_1]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [h719, hc34, hc45, hlam, hphi, p721_1]
                          · have p721_0 := h721c.1
                            have p721_1 := h721c.2.1
                            have p721_2 := h721c.2.2.1
                            have p721_3 := h721c.2.2.2
                            linarith only [hlam, p721_0]
                    · linarith only [h1, h560, h678, h708, h715, h716, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h678, h708, h711, h715, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h560, h711, h712, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h678, h708, h711, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h751 | h751
          · linarith only [h0, h4, h751, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h753 | h753
            · rcases m.htr 1 3 5 (by decide) (by decide) with h754 | h754
              · rcases m.htr 1 4 5 (by decide) (by decide) with h755 | h755
                · linarith only [h2, h561, h755, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h757 | h757
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h758 | h758
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h759 | h759
                      · linarith only [h2, h561, h708, h759, hc12, hlam, hphi, u2elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h761 | h761
                        · linarith only [h1, h753, h761, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases h5bigk with h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h3, h708, h755, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p763_1, u1elo0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h4, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h4, h761, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p763_1, u2elo4]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h561, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h3, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h751, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h761, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p763_1, u1elo4]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h755, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p763_1, u2elo4]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p763_1, u2elo4]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h758, h761, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p763_1, u2elo2]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h759, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h560, hlam, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h754, hlam, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h758, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h761, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h2, h561, h708, hc12, hc45, hlam, hphi, ht23, ht34, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h708, h755, hc12, hc45, hlam, hphi, ht23, ht34, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h0, h4, hc12, hc45, hlam, hphi, ht23, ht34, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h761, hc34, hc45, hlam, hphi, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hlam, p763_0]
                    · linarith only [h4, h560, h678, h758, hc12, hlam, hphi, u2elo4]
                  · linarith only [h678, h753, h757, hlam]
              · linarith only [h1, h560, h753, h754, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h792 | h792
              · rcases m.htr 1 4 5 (by decide) (by decide) with h793 | h793
                · linarith only [h2, h561, h793, hlam]
                · linarith only [h753, h792, h793, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h796 | h796
                · linarith only [h2, h560, h561, h792, h796, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h798 | h798
                  · linarith only [h678, h753, h798, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h800 | h800
                    · linarith only [h678, h792, h798, h800, hc12, hlam, hphi, u2elo3]
                    · linarith only [h1, h560, h678, h800, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h803 | h803
    · rcases m.htr 1 2 3 (by decide) (by decide) with h804 | h804
      · rcases m.htr 1 2 4 (by decide) (by decide) with h805 | h805
        · rcases m.htr 1 2 5 (by decide) (by decide) with h806 | h806
          · linarith only [h0, h4, h806, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h808 | h808
            · rcases m.htr 1 3 5 (by decide) (by decide) with h809 | h809
              · linarith only [h0, h4, h560, h804, h809, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h811 | h811
                · linarith only [h804, h806, h808, h811, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h813 | h813
                  · linarith only [h2, h803, h804, h806, h811, h813, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h2, h803, h804, h806, h808, h811, h813, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h816 | h816
              · linarith only [h1, h560, h816, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h818 | h818
                · linarith only [h805, h806, h818, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h820 | h820
                  · linarith only [h804, h808, h820, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h822 | h822
                    · linarith only [h1, h3, h560, h804, h805, h806, h822, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h824 | h824
                      · linarith only [h805, h806, h818, h824, hlam]
                      · linarith only [h0, h2, h4, h803, h805, h824, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h827 | h827
          · linarith only [h0, h4, h827, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h829 | h829
            · linarith only [h804, h805, h829, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h831 | h831
              · linarith only [h1, h560, h831, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h833 | h833
                · rcases m.htr 2 3 4 (by decide) (by decide) with h834 | h834
                  · linarith only [h0, h4, h804, h829, h834, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h836 | h836
                    · linarith only [h1, h560, h804, h836, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h839 | h839
                        · rcases h5bigk with h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [hlam, p840_0]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h804, h827, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p840_1]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h4, hlam, p840_0]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h560, hlam, p840_0]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h4, h838, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p840_1, u2elo3]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h3, hlam, p840_0]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [hlam, p840_0]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h827, hlam, p840_0]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h831, hlam, p840_0]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p840_1, u1elo4]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h838, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p840_1, u2elo3]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h838, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p840_1, u2elo3]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [hlam, p840_0]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h836, hlam, p840_1]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h838, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p840_1, u2elo3]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h0, h4, h804, h839, hc23, hc34, hlam, hphi, p840_1]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h804, h827, h839, hc23, hc34, hlam, hphi, p840_1]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h0, h4, h804, h839, hc23, hc34, hlam, hphi, p840_1]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [hlam, p840_0]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            rcases p840_3 (m.d 0 5) (by simp) with h860 | h860
                            · linarith only [h560, h860, hlam]
                            · linarith only [h803, h860, hlam]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h803, hlam, p840_1]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h833, hlam, p840_1]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h838, hlam, p840_1]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [h839, hlam, p840_1]
                          · have p840_0 := h840c.1
                            have p840_1 := h840c.2.1
                            have p840_2 := h840c.2.2.1
                            have p840_3 := h840c.2.2.2
                            linarith only [hlam, p840_0]
                        · linarith only [h2, h803, h829, h839, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h2, h833, h838, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h2, h803, h804, h805, h833, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h871 | h871
        · rcases m.htr 1 2 5 (by decide) (by decide) with h872 | h872
          · linarith only [h0, h4, h872, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h874 | h874
            · rcases m.htr 1 3 5 (by decide) (by decide) with h875 | h875
              · linarith only [h1, h560, h875, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h877 | h877
                · linarith only [h804, h871, h875, h877, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h879 | h879
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h880 | h880
                    · linarith only [h1, h560, h804, h880, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h882 | h882
                      · linarith only [h804, h871, h875, h877, h882, hlam]
                      · linarith only [h0, h2, h4, h803, h871, h879, h882, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h3, h804, h874, h875, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h804, h871, h874, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h887 | h887
          · linarith only [h4, h804, h887, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h889 | h889
            · rcases m.htr 1 3 5 (by decide) (by decide) with h890 | h890
              · linarith only [h1, h560, h890, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h892 | h892
                · linarith only [h889, h890, h892, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h894 | h894
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h895 | h895
                    · linarith only [h1, h560, h889, h895, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h897 | h897
                      · linarith only [h871, h892, h897, hc12, hlam, hphi, u2elo3]
                      · linarith only [h2, h803, h871, h897, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1, h889, h894, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h901 | h901
              · linarith only [h1, h560, h901, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h903 | h903
                · rcases m.htr 2 3 4 (by decide) (by decide) with h904 | h904
                  · linarith only [h804, h889, h904, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h906 | h906
                    · linarith only [h1, h560, h804, h906, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h908 | h908
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h909 | h909
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
                            linarith only [h3, h903, hc45, hlam, hphi, ht01, ht0b, ht5b, p910_1, u1elo0]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h4, hlam, p910_0]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h560, hlam, p910_0]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h4, h908, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p910_1, u2elo3]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h3, hlam, p910_0]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [hlam, p910_0]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h887, hlam, p910_0]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h901, hlam, p910_0]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p910_1, u1elo4]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h908, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p910_1, u2elo3]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h908, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p910_1, u2elo3]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [hlam, p910_0]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h906, hlam, p910_1]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h908, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p910_1, u2elo3]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h1, h560, h804, hc12, hc35, hlam, hphi, ht23, p910_1]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h804, h901, hc12, hc35, hlam, hphi, ht23, p910_1]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h906, hc23, hc35, hlam, hphi, p910_1]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [hlam, p910_0]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            rcases p910_3 (m.d 0 5) (by simp) with h930 | h930
                            · linarith only [h560, h930, hlam]
                            · linarith only [h803, h930, hlam]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h803, hlam, p910_1]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h903, hlam, p910_1]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h908, hlam, p910_1]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [h909, hlam, p910_1]
                          · have p910_0 := h910c.1
                            have p910_1 := h910c.2.1
                            have p910_2 := h910c.2.2.1
                            have p910_3 := h910c.2.2.2
                            linarith only [hlam, p910_0]
                        · linarith only [h4, h803, h804, h889, h909, hc12, hlam, hphi, u2elo4]
                      · linarith only [h2, h903, h908, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h940 | h940
                  · linarith only [h804, h889, h940, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h942 | h942
                    · linarith only [h1, h560, h804, h942, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h944 | h944
                      · linarith only [h804, h889, h903, h944, hc12, hlam, hphi, u2elo3]
                      · linarith only [h2, h803, h871, h944, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h947 | h947
      · rcases m.htr 1 2 4 (by decide) (by decide) with h948 | h948
        · rcases m.htr 1 2 5 (by decide) (by decide) with h949 | h949
          · linarith only [h0, h4, h949, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h951 | h951
            · rcases m.htr 1 3 5 (by decide) (by decide) with h952 | h952
              · linarith only [h1, h560, h952, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h954 | h954
                · linarith only [h2, h803, h954, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h956 | h956
                  · linarith only [h0, h4, h947, h956, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h1, h560, h951, h956, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h959 | h959
              · linarith only [h560, h951, h959, hc03, hc34, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h961 | h961
                · linarith only [h2, h803, h961, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h963 | h963
                  · linarith only [h0, h4, h947, h963, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h965 | h965
                    · linarith only [h0, h4, h560, h948, h963, h965, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h967 | h967
                      · linarith only [h0, h4, h803, h948, h967, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h969 | h969
                        · linarith only [h0, h4, h947, h967, h969, hc23, hc34, hlam, hphi]
                        · rcases h5bigk with h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h948, h949, h963, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h4, hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h560, hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h803, hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h3, hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h949, hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h959, hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h961, hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p971_1, u2elo4]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h948, h949, h963, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p971_1, u2elo4]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h965, hlam, p971_1]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h967, hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h3, h948, h949, h963, hc23, hc35, hlam, hphi, p971_1]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h948, h949, h963, h969, hc23, hc45, hlam, hphi, ht34, p971_1]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h4, h969, hc02, hc45, hlam, hphi, ht23, ht34, p971_1]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h969, hlam, p971_0]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h3, h948, h949, h963, hc23, hc45, hlam, hphi, ht34, p971_1]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h948, h949, h963, hc23, hc45, hlam, hphi, ht34, p971_1]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h0, h4, h948, h963, hc23, hc45, hlam, hphi, ht34, p971_1]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [h1, h560, h947, hc23, hc45, hlam, hphi, ht34, p971_1]
                          · have p971_0 := h971c.1
                            have p971_1 := h971c.2.1
                            have p971_2 := h971c.2.2.1
                            have p971_3 := h971c.2.2.2
                            linarith only [hlam, p971_0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h997 | h997
          · linarith only [h0, h4, h997, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h999 | h999
            · linarith only [h947, h948, h999, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1001 | h1001
              · linarith only [h0, h1001, h4, h560, h947, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1003 | h1003
                · linarith only [h1003, h2, h803, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1005 | h1005
                  · linarith only [h1005, h947, h948, h999, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1007 | h1007
                    · linarith only [h0, h1007, h4, h560, h947, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1009 | h1009
                      · linarith only [h1009, h2, h803, h948, hc12, hlam, hphi, u2elo3]
                      · linarith only [h1009, h947, h948, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1012 | h1012
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1013 | h1013
          · linarith only [h0, h1013, h4, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1015 | h1015
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1016 | h1016
              · linarith only [h1, h1016, h560, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1018 | h1018
                · linarith only [h1018, h2, h803, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1020 | h1020
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1021 | h1021
                    · linarith only [h1, h1021, h560, h947, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1023 | h1023
                      · linarith only [h1012, h1021, h1023, h803, h947, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1025 | h1025
                        · linarith only [h1020, h1023, h1025, h4, hc02, hlam, hphi, u2elo3]
                        · linarith only [h1012, h1020, h1021, h1025, h947, hc34, hc45, hlam, hphi]
                  · linarith only [h1015, h1020, h947, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · linarith only [h1012, h1015, h947, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1030 | h1030
          · linarith only [h1012, h1030, h4, hc02, hlam, hphi, u2elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1032 | h1032
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1033 | h1033
              · linarith only [h1, h1033, h560, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1035 | h1035
                · linarith only [h1, h1032, h1035, h803, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1037 | h1037
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1038 | h1038
                    · linarith only [h1, h1038, h560, h947, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1040 | h1040
                      · linarith only [h1012, h1037, h1038, h1040, h2, h803, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1042 | h1042
                        · linarith only [h1012, h1032, h1033, h1040, h1042, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h5bigk with h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1033, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1044_1, u2elo4]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h4, hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h560, hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h803, hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h3, hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1030, hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1033, hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1035, hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1044_1, u2elo4]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1033, h947, hc12, hlam, hphi, p1044_1, u2elo4]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1038, hlam, p1044_1]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1040, hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1012, h2, h803, hc12, hc35, hlam, hphi, ht23, p1044_1]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1032, h1033, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1044_1]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p1044_1]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1042, hlam, p1044_0]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1032, h1033, h3, hc34, hc45, hlam, hphi, p1044_1]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1032, h1033, hc34, hc45, hlam, hphi, p1044_1]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1012, h1037, h1038, hc12, hc45, hlam, hphi, ht23, ht34, p1044_1]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [h1, h1032, h560, hc34, hc45, hlam, hphi, p1044_1]
                          · have p1044_0 := h1044c.1
                            have p1044_1 := h1044c.2.1
                            have p1044_2 := h1044c.2.2.1
                            have p1044_3 := h1044c.2.2.2
                            linarith only [hlam, p1044_0]
                  · linarith only [h1, h1032, h1037, h560, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1071 | h1071
              · linarith only [h1032, h1071, h560, hc03, hc34, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1073 | h1073
                · linarith only [h1073, h2, h803, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1075 | h1075
                  · linarith only [h1032, h1075, h947, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1077 | h1077
                    · linarith only [h1, h1075, h1077, h560, h947, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1079 | h1079
                      · linarith only [h1012, h1079, h2, h803, hc12, hlam, hphi, u2elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1081 | h1081
                        · linarith only [h1075, h1079, h1081, h947, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h1075, h1081, h947, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1084 | h1084
  · linarith only [h0, h1084, h3, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1086 | h1086
    · linarith only [h1, h1086, h3, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1088 | h1088
      · linarith only [h1088, h2, h3, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1090 | h1090
        · linarith only [h0, h1090, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1092 | h1092
          · linarith only [h1, h1090, h1092, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1094 | h1094
            · linarith only [h1, h1084, h1090, h1094, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · linarith only [h1, h1090, h1094, h3, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3

set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1097 | h1097
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1098 | h1098
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1099 | h1099
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1100 | h1100
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1101 | h1101
          · linarith only [h0, h1101, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1103 | h1103
            · linarith only [h1, h1101, h1103, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
            · linarith only [h1, h1101, h1103, h2, hc12, hlam, hphi, u2elo3]
        · linarith only [h0, h1098, h1100, h2, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1107 | h1107
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1108 | h1108
          · linarith only [h0, h1108, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1110 | h1110
            · linarith only [h1, h1108, h1110, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
            · linarith only [h1, h1108, h1110, h2, hc12, hlam, hphi, u2elo3]
        · linarith only [h0, h1098, h1107, h2, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1114 | h1114
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1115 | h1115
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1116 | h1116
          · linarith only [h0, h1116, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1118 | h1118
            · linarith only [h1, h1116, h1118, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
            · linarith only [h1, h1116, h1118, h2, hc12, hlam, hphi, u2elo3]
        · linarith only [h1, h1114, h1115, h2, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1122 | h1122
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1123 | h1123
          · linarith only [h0, h1123, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1125 | h1125
            · linarith only [h1, h1123, h1125, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
            · linarith only [h1, h1123, h1125, h2, hc12, hlam, hphi, u2elo3]
        · linarith only [h1097, h1122, h2, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1129 | h1129
    · linarith only [h0, h1097, h1129, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1131 | h1131
      · linarith only [h1, h1097, h1131, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1133 | h1133
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1134 | h1134
          · linarith only [h0, h1134, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1136 | h1136
            · linarith only [h1, h1134, h1136, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
            · linarith only [h1, h1134, h1136, h2, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1139 | h1139
          · linarith only [h0, h1139, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1141 | h1141
            · linarith only [h1, h1139, h1141, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
            · linarith only [h1, h1139, h1141, h2, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2

set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1144 | h1144
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1145 | h1145
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1146 | h1146
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1147 | h1147
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1148 | h1148
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1149 | h1149
            · linarith only [h0, h1, h1149, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1149, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1152 | h1152
            · linarith only [h0, h1, h1152, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1152, hc12, hlam, hphi, u2elo2]
        · linarith only [h0, h1, h1146, h1147, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1156 | h1156
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1157 | h1157
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1158 | h1158
            · linarith only [h0, h1, h1158, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1158, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1161 | h1161
            · linarith only [h0, h1, h1161, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1161, hc12, hlam, hphi, u2elo2]
        · linarith only [h1, h1145, h1156, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1165 | h1165
      · linarith only [h0, h1145, h1165, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1167 | h1167
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1168 | h1168
          · linarith only [h1144, h1145, h1168, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1170 | h1170
            · linarith only [h0, h1, h1170, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1170, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1173 | h1173
          · linarith only [h1, h1144, h1167, h1173, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1175 | h1175
            · linarith only [h0, h1, h1175, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1175, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1178 | h1178
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1179 | h1179
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1180 | h1180
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1181 | h1181
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1182 | h1182
            · linarith only [h0, h1, h1182, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1182, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1144, h1179, h1181, hlam]
        · linarith only [h0, h1, h1179, h1180, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1187 | h1187
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1188 | h1188
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1189 | h1189
            · linarith only [h0, h1, h1189, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1189, hc12, hlam, hphi, u2elo2]
          · linarith only [h1144, h1178, h1188, hlam]
        · linarith only [h1, h1178, h1187, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1194 | h1194
      · linarith only [h0, h1178, h1194, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1196 | h1196
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1197 | h1197
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1198 | h1198
            · linarith only [h0, h1, h1198, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1198, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1201 | h1201
            · linarith only [h0, h1, h1201, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1201, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1204 | h1204
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1205 | h1205
            · linarith only [h0, h1, h1205, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1205, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1208 | h1208
            · linarith only [h0, h1, h1208, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h1208, hc12, hlam, hphi, u2elo2]

set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0 m hb1 hb2 hb4 hb5 h0 h1
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x1 m hb1 hb2 hb4 hb5 h0 h1

end R2N4
