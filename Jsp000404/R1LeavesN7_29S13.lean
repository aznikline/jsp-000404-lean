import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3078 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3604 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3605 | h3605
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3606 | h3606
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3607 | h3607
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3608 | h3608
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3609 | h3609
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3610 | h3610
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3611 | h3611
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3612 | h3612
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3613 | h3613
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3614 | h3614
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3615 | h3615
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3616 | h3616
                        · linarith only [h3078, h3604, h3616, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h3078, h3604, h3610, h3611, h3616, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h3078, h3605, h3606, h3609, h3615, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h3078, h3608, h3614, hlam]
                  · linarith only [h0, h3607, h3613, hlam]
                · linarith only [h0, h3604, h3612, hlam]
              · linarith only [h0, h3604, h3606, h3611, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3624 | h3624
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3625 | h3625
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3626 | h3626
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3627 | h3627
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3628 | h3628
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3629 | h3629
                        · linarith only [h3078, h3604, h3610, h3629, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3631 | h3631
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3632 | h3632
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3633 | h3633
                              · linarith only [h3078, h3604, h3610, h3624, h3625, h3633, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3635 | h3635
                                · linarith only [h3078, h3608, h3610, h3624, h3635, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                · rcases h1bigk with h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c | h3637c
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [hlam, p3637_0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h0, hlam, p3637_0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3078, hlam, p3637_0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3078, h3624, h3625, h3631, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3637_1, u1elo1]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3078, h3624, hc15, hlam, hphi, ht01, ht0b, ht5b, p3637_1, u1elo1]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [hc01, hlam, hphi, p3637_1, u1elo1]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [hlam, p3637_0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3078, hc01, hlam, hphi, p3637_1, u1elo1]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    rcases p3637_3 (m.d 0 1) (by simp) with h3646 | h3646
                                    · linarith only [h0, h3646, hlam]
                                    · linarith only [h3604, h3646, hlam]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    rcases p3637_3 (m.d 0 1) (by simp) with h3649 | h3649
                                    · linarith only [h0, h3649, hlam]
                                    · linarith only [h3605, h3649, hlam]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3605, h3625, h3629, h3631, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3637_1, u1elo2]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3624, hlam, p3637_1]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [hlam, p3637_0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    rcases p3637_3 (m.d 0 1) (by simp) with h3655 | h3655
                                    · linarith only [h3078, h3655, hlam]
                                    · linarith only [h3604, h3655, hlam]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    rcases p3637_3 (m.d 0 1) (by simp) with h3658 | h3658
                                    · linarith only [h3078, h3658, hlam]
                                    · linarith only [h3605, h3658, hlam]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3604, hlam, p3637_0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3625, hlam, p3637_1]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3627, hlam, p3637_0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [hlam, p3637_0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3629, hlam, p3637_1]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3605, hlam, p3637_0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3626, hlam, p3637_1]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3628, hlam, p3637_0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [h3605, h3625, h3631, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3637_1, u1elo0]
                                  · have p3637_0 := h3637c.1
                                    have p3637_1 := h3637c.2.1
                                    have p3637_2 := h3637c.2.2.1
                                    have p3637_3 := h3637c.2.2.2
                                    linarith only [hlam, p3637_0]
                            · linarith only [h3078, h3605, h3624, h3628, h3632, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h3078, h3604, h3624, h3627, h3631, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3078, h3606, h3609, h3628, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h3078, h3606, h3608, h3627, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h3605, h3607, h3626, hlam]
                · linarith only [h3078, h3604, h3624, h3625, hlam]
              · linarith only [h0, h3604, h3606, h3624, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h3078, h3605, h3609, hlam]
        · linarith only [h3078, h3604, h3608, hlam]
      · linarith only [h0, h3605, h3607, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3681 | h3681
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3682 | h3682
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3683 | h3683
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3684 | h3684
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3685 | h3685
              · linarith only [h0, h3604, h3606, h3685, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3687 | h3687
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3688 | h3688
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3689 | h3689
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3690 | h3690
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3691 | h3691
                        · linarith only [h0, h3604, h3691, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h0, h3604, h3684, h3685, h3691, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h3078, h3605, h3683, h3690, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h3078, h3682, h3689, hlam]
                  · linarith only [h0, h3604, h3681, h3687, h3688, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h3604, h3687, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3698 | h3698
              · linarith only [h3606, h3681, h3698, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3700 | h3700
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3701 | h3701
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3702 | h3702
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3703 | h3703
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3704 | h3704
                        · linarith only [h3604, h3684, h3704, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3706 | h3706
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3707 | h3707
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3708 | h3708
                              · linarith only [h3604, h3684, h3700, h3708, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3710 | h3710
                                · linarith only [h3604, h3684, h3700, h3706, h3710, hlam]
                                · rcases h1bigk with h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h0, hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3078, hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h0, h3698, h3700, h3706, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3712_1]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h0, h3698, h3700, h3704, h3706, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3712_1]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3698, hc01, hc23, hlam, hphi, ht12, p3712_1]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3698, hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    rcases p3712_3 (m.d 0 1) (by simp) with h3721 | h3721
                                    · linarith only [h0, h3721, hlam]
                                    · linarith only [h3604, h3721, hlam]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    rcases p3712_3 (m.d 0 1) (by simp) with h3724 | h3724
                                    · linarith only [h0, h3724, hlam]
                                    · linarith only [h3605, h3724, hlam]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3605, h3700, h3704, h3706, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3712_1, u1elo2]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h0, h3605, h3700, h3704, h3706, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3712_1, u1elo2]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    rcases p3712_3 (m.d 0 1) (by simp) with h3730 | h3730
                                    · linarith only [h3078, h3730, hlam]
                                    · linarith only [h3604, h3730, hlam]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    rcases p3712_3 (m.d 0 1) (by simp) with h3733 | h3733
                                    · linarith only [h3078, h3733, hlam]
                                    · linarith only [h3605, h3733, hlam]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3604, hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3700, hlam, p3712_1]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3702, hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3704, hlam, p3712_1]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3605, hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3701, hlam, p3712_1]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h3703, hlam, p3712_0]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [h0, h3605, h3700, h3706, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3712_1, u1elo1]
                                  · have p3712_0 := h3712c.1
                                    have p3712_1 := h3712c.2.1
                                    have p3712_2 := h3712c.2.2.1
                                    have p3712_3 := h3712c.2.2.2
                                    linarith only [hlam, p3712_0]
                            · linarith only [h0, h3605, h3698, h3703, h3707, hlam]
                          · linarith only [h0, h3698, h3706, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h3078, h3683, h3703, hlam]
                    · linarith only [h3078, h3682, h3702, hlam]
                  · linarith only [h0, h3604, h3681, h3700, h3701, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h3604, h3700, hlam]
          · linarith only [h3078, h3605, h3683, hlam]
        · linarith only [h0, h3604, h3606, h3682, hlam]
      · linarith only [h0, h3605, h3681, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3755 | h3755
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3756 | h3756
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3757 | h3757
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3758 | h3758
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3759 | h3759
            · linarith only [h3604, h3605, h3759, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3761 | h3761
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3762 | h3762
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3763 | h3763
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3764 | h3764
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3765 | h3765
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3766 | h3766
                        · linarith only [h3604, h3605, h3759, h3761, h3765, h3766, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3768 | h3768
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3769 | h3769
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3770 | h3770
                              · linarith only [h3604, h3605, h3762, h3766, h3770, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3772 | h3772
                                · linarith only [h3605, h3755, h3766, h3768, h3772, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases h1bigk with h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c | h3774c
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [hlam, p3774_0]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h0, hlam, p3774_0]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3078, hlam, p3774_0]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3605, h3762, h3765, h3768, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3774_1, u1elo2]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3605, hlam, p3774_0]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [hc01, hlam, hphi, p3774_1, u1elo1]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [hlam, p3774_0]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3078, h3604, h3762, h3768, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3774_1, u1elo1]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    rcases p3774_3 (m.d 0 1) (by simp) with h3783 | h3783
                                    · linarith only [h0, h3783, hlam]
                                    · linarith only [h3604, h3783, hlam]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3604, h3605, h3762, h3768, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3774_1, u1elo1]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3604, h3762, h3768, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3774_1, u1elo2]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3761, hlam, p3774_1]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [hlam, p3774_0]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    rcases p3774_3 (m.d 0 1) (by simp) with h3790 | h3790
                                    · linarith only [h3078, h3790, hlam]
                                    · linarith only [h3604, h3790, hlam]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3604, h3605, h3761, h3762, h3768, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3774_1, u1elo1]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3604, hlam, p3774_0]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3762, hlam, p3774_1]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3764, hlam, p3774_0]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [hlam, p3774_0]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3766, hlam, p3774_1]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3604, h3762, h3768, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3774_1, u1elo4]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3763, hlam, p3774_1]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [h3765, hlam, p3774_0]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    rcases p3774_3 (m.d 0 1) (by simp) with h3802 | h3802
                                    · linarith only [h3605, h3802, hlam]
                                    · linarith only [h3604, h3802, hlam]
                                  · have p3774_0 := h3774c.1
                                    have p3774_1 := h3774c.2.1
                                    have p3774_2 := h3774c.2.2.1
                                    have p3774_3 := h3774c.2.2.2
                                    linarith only [hlam, p3774_0]
                            · linarith only [h3078, h3758, h3761, h3768, h3769, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h3604, h3605, h3761, h3764, h3765, h3768, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h3078, h3758, h3765, hlam]
                    · linarith only [h3078, h3757, h3764, hlam]
                  · linarith only [h0, h3605, h3756, h3763, hc01, hlam, hphi, u1elo4]
                · linarith only [h3078, h3604, h3761, h3762, hlam]
              · linarith only [h0, h3604, h3755, h3761, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3813 | h3813
            · linarith only [h3078, h3604, h3758, h3813, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3815 | h3815
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3816 | h3816
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3817 | h3817
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3818 | h3818
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3819 | h3819
                      · linarith only [h3078, h3604, h3758, h3816, h3819, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3821 | h3821
                        · linarith only [h3604, h3813, h3821, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3823 | h3823
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3824 | h3824
                            · linarith only [h3078, h3819, h3824, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3826 | h3826
                              · linarith only [h3078, h3604, h3605, h3816, h3819, h3821, h3826, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3828 | h3828
                                · linarith only [h3078, h3604, h3605, h3758, h3816, h3819, h3821, h3823, h3828, hc03, hc35, hlam, hphi]
                                · linarith only [h3078, h3604, h3816, h3819, h3823, h3828, hc34, hc45, hlam, hphi]
                          · linarith only [h3078, h3757, h3819, h3823, hc23, hc35, hlam, hphi]
                    · linarith only [h3078, h3604, h3757, h3818, hlam]
                  · linarith only [h0, h3756, h3817, hlam]
                · linarith only [h0, h3078, h3604, h3756, h3816, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · linarith only [h0, h3604, h3755, h3815, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h3078, h3604, h3757, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3837 | h3837
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3838 | h3838
          · linarith only [h3755, h3756, h3838, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3840 | h3840
            · linarith only [h0, h3604, h3756, h3840, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3842 | h3842
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3843 | h3843
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3844 | h3844
                  · linarith only [h3078, h3755, h3756, h3844, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3846 | h3846
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3847 | h3847
                      · linarith only [h3078, h3604, h3838, h3842, h3843, h3844, h3847, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3849 | h3849
                        · linarith only [h3604, h3840, h3849, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3851 | h3851
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3852 | h3852
                            · linarith only [h3078, h3755, h3847, h3852, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3854 | h3854
                              · linarith only [h3078, h3604, h3605, h3842, h3843, h3844, h3849, h3852, h3854, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h3078, h3604, h3842, h3843, h3844, h3851, h3854, hc34, hc45, hlam, hphi]
                          · linarith only [h3837, h3838, h3851, hc23, hc35, hlam, hphi]
                    · linarith only [h3078, h3837, h3838, h3846, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h3604, h3843, hlam]
              · linarith only [h0, h3604, h3755, h3842, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h3078, h3604, h3837, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3862 | h3862
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3863 | h3863
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3864 | h3864
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3865 | h3865
            · linarith only [h3604, h3605, h3865, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3867 | h3867
              · linarith only [h0, h3604, h3755, h3867, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3869 | h3869
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3870 | h3870
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3871 | h3871
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3872 | h3872
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3873 | h3873
                        · linarith only [h3604, h3865, h3873, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3875 | h3875
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3876 | h3876
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3877 | h3877
                              · linarith only [h3604, h3605, h3869, h3873, h3877, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3879 | h3879
                                · linarith only [h3604, h3605, h3869, h3873, h3875, h3879, hlam]
                                · rcases h1bigk with h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c | h3881c
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h0, hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3078, hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3605, h3867, h3870, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3881_1]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3605, hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3867, hc01, hc23, hlam, hphi, ht12, p3881_1]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3867, hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    rcases p3881_3 (m.d 0 1) (by simp) with h3890 | h3890
                                    · linarith only [h0, h3890, hlam]
                                    · linarith only [h3604, h3890, hlam]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3604, h3605, h3867, h3869, h3875, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3881_1]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3604, h3869, h3875, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3881_1, u1elo2]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h0, h3604, h3869, h3875, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3881_1, u1elo2]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    rcases p3881_3 (m.d 0 1) (by simp) with h3897 | h3897
                                    · linarith only [h3078, h3897, hlam]
                                    · linarith only [h3604, h3897, hlam]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3604, h3605, h3869, h3875, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3881_1, u1elo2]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3604, hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3869, hlam, p3881_1]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3871, hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3873, hlam, p3881_1]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3604, h3869, h3870, h3875, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3881_1, u1elo1]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3870, hlam, p3881_1]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [h3872, hlam, p3881_0]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    rcases p3881_3 (m.d 0 1) (by simp) with h3909 | h3909
                                    · linarith only [h3605, h3909, hlam]
                                    · linarith only [h3604, h3909, hlam]
                                  · have p3881_0 := h3881c.1
                                    have p3881_1 := h3881c.2.1
                                    have p3881_2 := h3881c.2.2.1
                                    have p3881_3 := h3881c.2.2.2
                                    linarith only [hlam, p3881_0]
                            · linarith only [h0, h3604, h3867, h3869, h3875, h3876, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h3867, h3875, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h3078, h3604, h3864, h3869, h3872, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h3078, h3863, h3871, hlam]
                  · linarith only [h0, h3604, h3862, h3869, h3870, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h3604, h3869, hlam]
          · linarith only [h3755, h3862, h3864, hlam]
        · linarith only [h0, h3604, h3755, h3863, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3921 | h3921
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3922 | h3922
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3923 | h3923
            · linarith only [h0, h3604, h3862, h3923, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3925 | h3925
              · linarith only [h0, h3755, h3925, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3927 | h3927
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3928 | h3928
                  · linarith only [h0, h3604, h3862, h3927, h3928, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3930 | h3930
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3931 | h3931
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3932 | h3932
                        · linarith only [h3604, h3923, h3932, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3934 | h3934
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3935 | h3935
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3936 | h3936
                              · linarith only [h0, h3927, h3928, h3932, h3936, hc01, hlam, hphi, u1elo3]
                              · linarith only [h0, h3604, h3927, h3928, h3934, h3936, hc34, hc45, hlam, hphi]
                            · linarith only [h0, h3604, h3755, h3922, h3927, h3934, h3935, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h3925, h3934, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h3078, h3604, h3922, h3927, h3931, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h3078, h3921, h3930, hlam]
                · linarith only [h0, h3604, h3927, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3944 | h3944
            · linarith only [h3078, h3604, h3922, h3944, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3946 | h3946
              · linarith only [h0, h3755, h3946, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3948 | h3948
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3949 | h3949
                  · linarith only [h0, h3604, h3862, h3946, h3948, h3949, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3951 | h3951
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3952 | h3952
                      · linarith only [h0, h3604, h3755, h3922, h3948, h3952, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3954 | h3954
                        · linarith only [h3604, h3944, h3954, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3956 | h3956
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3957 | h3957
                            · linarith only [h0, h3946, h3952, h3957, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h3604, h3946, h3948, h3956, h3957, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h3946, h3956, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h3604, h3921, h3946, h3951, hlam]
                · linarith only [h0, h3604, h3948, hlam]
        · linarith only [h0, h3604, h3755, h3921, hlam]

set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3078 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3604 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3964 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3965 | h3965
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3966 | h3966
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3967 | h3967
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3968 | h3968
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3969 | h3969
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3970 | h3970
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3971 | h3971
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3972 | h3972
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3973 | h3973
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3974 | h3974
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3975 | h3975
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3976 | h3976
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3977 | h3977
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3978 | h3978
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3979 | h3979
                              · linarith only [h0, h3965, h3976, h3979, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · linarith only [h0, h3964, h3975, h3979, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h3604, h3964, h3970, h3973, h3975, h3978, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h3604, h3964, h3970, h3973, h3974, h3977, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3984 | h3984
                          · linarith only [h0, h3965, h3967, h3976, h3984, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h3604, h3964, h3970, h3973, h3974, h3984, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3604, h3965, h3967, h3969, h3975, hc01, hlam, hphi, u1elo1]
                    · linarith only [h3604, h3964, h3968, h3973, h3974, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3078, h3967, h3973, hlam]
                · linarith only [h0, h3966, h3972, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3991 | h3991
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3992 | h3992
                  · linarith only [h3970, h3971, h3992, hlam]
                  · linarith only [h3078, h3967, h3992, hlam]
                · linarith only [h0, h3966, h3991, hlam]
            · linarith only [h0, h3965, h3970, hlam]
          · linarith only [h3604, h3964, h3969, hlam]
        · linarith only [h3078, h3964, h3968, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3999 | h3999
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4000 | h4000
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4001 | h4001
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4002 | h4002
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4003 | h4003
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4004 | h4004
                  · linarith only [h3078, h3967, h4004, hc01, hlam, hphi, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4006 | h4006
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4007 | h4007
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4008 | h4008
                        · linarith only [h0, h3965, h4004, h4008, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4010 | h4010
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4011 | h4011
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4012 | h4012
                              · rcases h1bigk with h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c | h4013c
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [hlam, p4013_0]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h0, hlam, p4013_0]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h3078, hlam, p4013_0]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h3604, hlam, p4013_0]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h3078, h4003, h4004, h4010, h4012, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4013_1]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [hc01, hlam, hphi, p4013_1, u1elo1]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [hlam, p4013_0]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h3078, h3964, h4003, h4010, h4012, hc45, hlam, hphi, ht01, ht0b, ht5b, p4013_1, u1elo1]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h3604, h3964, h4003, h4010, h4012, hc45, hlam, hphi, ht01, ht0b, ht5b, p4013_1, u1elo1]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  rcases p4013_3 (m.d 0 1) (by simp) with h4023 | h4023
                                  · linarith only [h0, h4023, hlam]
                                  · linarith only [h3964, h4023, hlam]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h3964, h4003, h4010, h4012, hc45, hlam, hphi, ht01, ht0b, ht5b, p4013_1, u1elo2]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h4001, hlam, p4013_1]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [hlam, p4013_0]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h4004, hlam, p4013_1]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  rcases p4013_3 (m.d 0 1) (by simp) with h4030 | h4030
                                  · linarith only [h3078, h4030, hlam]
                                  · linarith only [h3964, h4030, hlam]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h3964, h4002, h4003, h4010, h4012, hc45, hlam, hphi, ht01, ht0b, ht5b, p4013_1, u1elo1]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h4002, hlam, p4013_1]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h3078, h3964, h4002, h4003, h4010, h4012, hc45, hlam, hphi, ht01, ht0b, ht5b, p4013_1, u1elo1]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [hlam, p4013_0]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  rcases p4013_3 (m.d 0 1) (by simp) with h4037 | h4037
                                  · linarith only [h3604, h4037, hlam]
                                  · linarith only [h3964, h4037, hlam]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h3964, hlam, p4013_0]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h4003, hlam, p4013_1]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h4006, hlam, p4013_0]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [h4007, hlam, p4013_0]
                                · have p4013_0 := h4013c.1
                                  have p4013_1 := h4013c.2.1
                                  have p4013_2 := h4013c.2.2.1
                                  have p4013_3 := h4013c.2.2.2
                                  linarith only [hlam, p4013_0]
                              · linarith only [h3078, h3964, h3967, h4000, h4012, hc04, hc15, hlam, hphi, ht0b, ht5b]
                            · linarith only [h3078, h3964, h4002, h4004, h4007, h4011, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h3078, h3999, h4004, h4010, hc23, hc34, hlam, hphi]
                      · linarith only [h3604, h4000, h4007, hlam]
                    · linarith only [h3078, h3964, h3999, h4006, hc03, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h3966, h4003, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4051 | h4051
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4052 | h4052
                  · linarith only [h3078, h3967, h4052, hc01, hlam, hphi, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4054 | h4054
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4055 | h4055
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4056 | h4056
                        · linarith only [h3078, h3964, h4051, h4052, h4056, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4058 | h4058
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4059 | h4059
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4060 | h4060
                              · rcases h1bigk with h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h0, hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h3078, hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h3604, hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h3078, h4051, h4058, h4060, hc45, hlam, hphi, ht01, ht0b, ht5b, p4061_1, u1elo2]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h4002, h4056, hc01, hc34, hlam, hphi, ht12, ht23, p4061_1]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h4002, h4056, hc13, hc34, hlam, hphi, p4061_1]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h4002, hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  rcases p4061_3 (m.d 0 1) (by simp) with h4071 | h4071
                                  · linarith only [h0, h4071, hlam]
                                  · linarith only [h3964, h4071, hlam]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h3964, h4051, h4058, h4060, hc45, hlam, hphi, ht01, ht0b, ht5b, p4061_1, u1elo2]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h4001, hlam, p4061_1]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h4052, hlam, p4061_1]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  rcases p4061_3 (m.d 0 1) (by simp) with h4078 | h4078
                                  · linarith only [h3078, h4078, hlam]
                                  · linarith only [h3964, h4078, hlam]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h3964, h4051, h4058, h4060, hc45, hlam, hphi, ht01, ht0b, ht5b, p4061_1, u1elo3]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h0, h3964, h4051, h4058, h4060, hc45, hlam, hphi, ht01, ht0b, ht5b, p4061_1, u1elo3]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h3078, h3964, h4051, h4058, h4060, hc45, hlam, hphi, ht01, ht0b, ht5b, p4061_1, u1elo3]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  rcases p4061_3 (m.d 0 1) (by simp) with h4085 | h4085
                                  · linarith only [h3604, h4085, hlam]
                                  · linarith only [h3964, h4085, hlam]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h3964, hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h4051, hlam, p4061_1]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h4054, hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [h4055, hlam, p4061_0]
                                · have p4061_0 := h4061c.1
                                  have p4061_1 := h4061c.2.1
                                  have p4061_2 := h4061c.2.2.1
                                  have p4061_3 := h4061c.2.2.2
                                  linarith only [hlam, p4061_0]
                              · linarith only [h3967, h4000, h4060, hlam]
                            · linarith only [h3078, h3964, h4001, h4002, h4055, h4059, hlam]
                          · linarith only [h3078, h3999, h4001, h4002, h4056, h4058, hc23, hc34, hlam, hphi]
                      · linarith only [h3604, h4000, h4055, hlam]
                    · linarith only [h3078, h3999, h4054, hlam]
                · linarith only [h0, h3966, h4051, hlam]
            · linarith only [h0, h3965, h4001, hlam]
          · linarith only [h3604, h3964, h4000, hlam]
        · linarith only [h3078, h3964, h3999, hlam]
    · linarith only [h0, h3964, h3966, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4103 | h4103
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4104 | h4104
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4105 | h4105
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4106 | h4106
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4107 | h4107
            · linarith only [h0, h3965, h4107, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4109 | h4109
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4110 | h4110
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4111 | h4111
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4112 | h4112
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4113 | h4113
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4114 | h4114
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4115 | h4115
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4116 | h4116
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4117 | h4117
                              · rcases h1bigk with h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h0, hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h3078, hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h3604, hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h3604, h4109, h4110, h4115, h4117, hc45, hlam, hphi, ht01, ht0b, ht5b, p4118_1, u1elo1]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h4107, hc01, hlam, hphi, p4118_1, u1elo2]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h4107, hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h3604, h4107, hc01, hlam, hphi, p4118_1, u1elo2]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  rcases p4118_3 (m.d 0 1) (by simp) with h4128 | h4128
                                  · linarith only [h0, h4128, hlam]
                                  · linarith only [h3964, h4128, hlam]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h3964, h4110, h4115, h4117, hc45, hlam, hphi, ht01, ht0b, ht5b, p4118_1, u1elo2]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h4109, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4118_1, u1elo2]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h3604, h3964, h4110, h4115, h4117, hc45, hlam, hphi, ht01, ht0b, ht5b, p4118_1, u1elo2]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  rcases p4118_3 (m.d 0 1) (by simp) with h4135 | h4135
                                  · linarith only [h3078, h4135, hlam]
                                  · linarith only [h3964, h4135, hlam]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h3964, h4109, h4110, h4115, h4117, hc45, hlam, hphi, ht01, ht0b, ht5b, p4118_1, u1elo1]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h4109, hlam, p4118_1]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h4111, hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  rcases p4118_3 (m.d 0 1) (by simp) with h4142 | h4142
                                  · linarith only [h3604, h4142, hlam]
                                  · linarith only [h3964, h4142, hlam]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h3964, hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h4110, hlam, p4118_1]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h4112, hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [h4113, hlam, p4118_0]
                                · have p4118_0 := h4118c.1
                                  have p4118_1 := h4118c.2.1
                                  have p4118_2 := h4118c.2.2.1
                                  have p4118_3 := h4118c.2.2.2
                                  linarith only [hlam, p4118_0]
                              · linarith only [h0, h3964, h4107, h4113, h4117, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h3604, h3964, h4107, h4109, h4113, h4116, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h3604, h4107, h4109, h4115, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h3604, h3964, h4107, h4109, h4113, h4114, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h3604, h4106, h4113, hlam]
                    · linarith only [h3078, h3964, h4105, h4112, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3078, h4104, h4111, hlam]
                · linarith only [h3604, h3964, h4103, h4109, h4110, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4158 | h4158
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4159 | h4159
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4160 | h4160
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4161 | h4161
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4162 | h4162
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4163 | h4163
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4164 | h4164
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4165 | h4165
                              · rcases h1bigk with h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h0, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h3078, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h3604, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h0, h4158, h4163, h4165, hc45, hlam, hphi, ht01, ht0b, ht5b, p4166_1, u1elo1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hc01, hlam, hphi, p4166_1, u1elo1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h4107, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h4109, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  rcases p4166_3 (m.d 0 1) (by simp) with h4176 | h4176
                                  · linarith only [h0, h4176, hlam]
                                  · linarith only [h3964, h4176, hlam]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h3964, h4158, h4163, h4165, hc45, hlam, hphi, ht01, ht0b, ht5b, p4166_1, u1elo2]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h0, h3964, h4158, h4163, h4165, hc45, hlam, hphi, ht01, ht0b, ht5b, p4166_1, u1elo2]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h3604, h3964, h4158, h4163, h4165, hc45, hlam, hphi, ht01, ht0b, ht5b, p4166_1, u1elo2]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  rcases p4166_3 (m.d 0 1) (by simp) with h4183 | h4183
                                  · linarith only [h3078, h4183, hlam]
                                  · linarith only [h3964, h4183, hlam]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h3964, h4158, h4163, h4165, hc45, hlam, hphi, ht01, ht0b, ht5b, p4166_1, u1elo3]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h0, h3964, h4158, h4163, h4165, hc45, hlam, hphi, ht01, ht0b, ht5b, p4166_1, u1elo3]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h4159, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  rcases p4166_3 (m.d 0 1) (by simp) with h4190 | h4190
                                  · linarith only [h3604, h4190, hlam]
                                  · linarith only [h3964, h4190, hlam]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h3964, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h4158, hlam, p4166_1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h4160, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h4161, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hlam, p4166_0]
                              · linarith only [h0, h3964, h4109, h4161, h4162, h4165, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h3964, h4109, h4161, h4164, hlam]
                          · linarith only [h0, h4109, h4162, h4163, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h3965, h4104, h4162, hlam]
                      · linarith only [h0, h3078, h4104, h4106, h4109, h4161, hc01, hlam, hphi, u1elo2]
                    · linarith only [h0, h3964, h4105, h4109, h4159, h4160, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3078, h3964, h4104, h4159, hc03, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h3964, h4103, h4158, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h3604, h3964, h4106, hlam]
        · linarith only [h0, h3964, h3965, h4105, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4208 | h4208
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4209 | h4209
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4210 | h4210
            · linarith only [h0, h3964, h3965, h4210, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4212 | h4212
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4213 | h4213
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4214 | h4214
                  · linarith only [h0, h3964, h3965, h4104, h4213, h4214, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · linarith only [h4210, h4212, h4214, hlam]
                · linarith only [h0, h4103, h4213, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4218 | h4218
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4219 | h4219
                  · linarith only [h0, h3964, h3965, h4104, h4218, h4219, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4221 | h4221
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4222 | h4222
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4223 | h4223
                        · linarith only [h0, h3964, h4210, h4218, h4219, h4223, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h3964, h4210, h4218, h4223, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h3604, h4209, h4222, hlam]
                    · linarith only [h0, h3964, h4208, h4210, h4218, h4221, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h3964, h4103, h4218, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h3964, h3965, h4104, h4209, hlam]
        · linarith only [h0, h3964, h3965, h4208, hlam]
    · linarith only [h0, h3964, h4103, hlam]

end R2N4
