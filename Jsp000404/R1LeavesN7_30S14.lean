import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5764000 in
set_option maxHeartbeats 5764000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1106 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1991 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2808 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3661 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1106 := hg1106
  rcases m.htr 0 2 5 (by decide) (by decide) with h3662 | h3662
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3663 | h3663
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3664 | h3664
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3665 | h3665
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3666 | h3666
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3667 | h3667
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3668 | h3668
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3669 | h3669
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3670 | h3670
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3671 | h3671
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3672 | h3672
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3673 | h3673
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3674 | h3674
                          · linarith only [h2808, h3661, h3674, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h2808, h3661, h3665, h3674, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h2808, h3664, h3673, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2808, h3661, h3663, h3665, h3672, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h3661, h3665, h3671, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h2808, h3664, h3666, h3670, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2808, h3661, h3663, h3666, h3669, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h2808, h3661, h3666, h3668, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h2808, h3661, h3666, h3667, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3684 | h3684
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3685 | h3685
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3686 | h3686
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3687 | h3687
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3688 | h3688
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3689 | h3689
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3690 | h3690
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3691 | h3691
                          · linarith only [h3661, h3691, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h3665, h3691, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h2808, h3664, h3690, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h3666, h3689, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1991, h3665, h3688, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1106, h3664, h3687, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                · linarith only [h1106, h3663, h3686, hlam]
              · linarith only [h0, h3662, h3685, hlam]
            · linarith only [h0, h3661, h3684, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3701 | h3701
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3702 | h3702
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3703 | h3703
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3704 | h3704
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3705 | h3705
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3706 | h3706
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3707 | h3707
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3708 | h3708
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3709 | h3709
                          · linarith only [h2808, h3661, h3665, h3709, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3711 | h3711
                            · linarith only [h1991, h2808, h3662, h3665, h3701, h3707, h3709, h3711, hc01, hc12, hlam, hphi]
                            · rcases h2bigk with h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c | h3713c
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [hlam, p3713_0]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h0, hlam, p3713_1]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h2808, hlam, p3713_0]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h2808, hc24, hlam, hphi, ht0b, ht45, ht5b, p3713_1, u0elo2]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h2808, hc25, hlam, hphi, ht0b, ht5b, p3713_1, u0elo2]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                rcases p3713_3 (m.d 0 2) (by simp) with h3719 | h3719
                                · linarith only [h0, h3719, hlam]
                                · rcases p3713_3 (m.d 1 2) (by simp) with h3721 | h3721
                                  · rcases p3713_3 (m.d 2 3) (by simp) with h3722 | h3722
                                    · linarith only [h3701, h3722, hlam]
                                    · linarith only [h2808, h3722, hlam]
                                  · linarith only [h0, h3721, hlam]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [hlam, p3713_0]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h0, h2808, hc01, hc12, hlam, hphi, p3713_1]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h2808, h3662, h3701, h3709, hlam, p3713_2]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h2808, h3662, h3701, hlam, p3713_2]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h3662, h3701, h3707, h3709, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3713_1]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h3701, hlam, p3713_0]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [hlam, p3713_0]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                rcases p3713_3 (m.d 0 2) (by simp) with h3733 | h3733
                                · linarith only [h2808, h3733, hlam]
                                · linarith only [h3661, h3733, hlam]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                rcases p3713_3 (m.d 0 2) (by simp) with h3736 | h3736
                                · linarith only [h2808, h3736, hlam]
                                · linarith only [h3662, h3736, hlam]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h3661, hlam, p3713_0]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h3702, hlam, p3713_0]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h3707, hlam, p3713_1]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [hlam, p3713_0]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h3709, hlam, p3713_1]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h3662, hlam, p3713_0]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h3703, hlam, p3713_0]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h3708, hlam, p3713_1]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [h3662, h3707, hc34, hlam, hphi, ht0b, ht45, ht5b, p3713_1, u0elo1]
                              · have p3713_0 := h3713c.1
                                have p3713_1 := h3713c.2.1
                                have p3713_2 := h3713c.2.2.1
                                have p3713_3 := h3713c.2.2.2
                                linarith only [hlam, p3713_0]
                        · linarith only [h2808, h3664, h3708, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2808, h3661, h3663, h3707, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3751 | h3751
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3752 | h3752
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3753 | h3753
                          · linarith only [h3661, h3706, h3753, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3755 | h3755
                            · linarith only [h1991, h3662, h3706, h3751, h3753, h3755, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases h2bigk with h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c | h3757c
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [hlam, p3757_0]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h0, hlam, p3757_1]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h2808, hlam, p3757_0]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h2808, h3701, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3757_1]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h2808, h3701, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3757_1]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                rcases p3757_3 (m.d 0 2) (by simp) with h3763 | h3763
                                · linarith only [h0, h3763, hlam]
                                · rcases p3757_3 (m.d 1 2) (by simp) with h3765 | h3765
                                  · rcases p3757_3 (m.d 2 3) (by simp) with h3766 | h3766
                                    · linarith only [h3701, h3766, hlam]
                                    · linarith only [h2808, h3766, hlam]
                                  · linarith only [h0, h3765, hlam]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [hlam, p3757_0]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h0, h2808, hc01, hc12, hlam, hphi, p3757_1]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h2808, h3662, h3701, h3753, hlam, p3757_2]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h2808, h3662, h3701, hlam, p3757_2]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h3662, h3701, h3751, h3753, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3757_1]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h3701, hlam, p3757_0]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [hlam, p3757_0]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                rcases p3757_3 (m.d 0 2) (by simp) with h3777 | h3777
                                · linarith only [h2808, h3777, hlam]
                                · linarith only [h3661, h3777, hlam]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                rcases p3757_3 (m.d 0 2) (by simp) with h3780 | h3780
                                · linarith only [h2808, h3780, hlam]
                                · linarith only [h3662, h3780, hlam]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h3661, hlam, p3757_0]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h3702, hlam, p3757_0]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h3751, hlam, p3757_1]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [hlam, p3757_0]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h3753, hlam, p3757_1]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h3662, hlam, p3757_0]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h3703, hlam, p3757_0]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h3752, hlam, p3757_1]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [h3662, h3751, hc34, hlam, hphi, ht0b, ht45, ht5b, p3757_1, u0elo1]
                              · have p3757_0 := h3757c.1
                                have p3757_1 := h3757c.2.1
                                have p3757_2 := h3757c.2.2.1
                                have p3757_3 := h3757c.2.2.2
                                linarith only [hlam, p3757_0]
                        · linarith only [h2808, h3664, h3752, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2808, h3661, h3663, h3751, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h2808, h3661, h3664, h3701, h3705, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h2808, h3661, h3663, h3701, h3704, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h3662, h3703, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2808, h3701, h3702, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3799 | h3799
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3800 | h3800
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3801 | h3801
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3802 | h3802
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3803 | h3803
                    · linarith only [h1991, h3665, h3701, h3799, h3803, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3805 | h3805
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3806 | h3806
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3807 | h3807
                          · linarith only [h3661, h3803, h3807, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3809 | h3809
                            · linarith only [h1991, h3803, h3809, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h2bigk with h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c | h3811c
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [hlam, p3811_0]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h0, hlam, p3811_1]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h2808, hlam, p3811_0]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h2808, hc24, hlam, hphi, ht0b, ht45, ht5b, p3811_1, u0elo2]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h2808, hc25, hlam, hphi, ht0b, ht5b, p3811_1, u0elo2]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h3701, hc02, hc23, hlam, hphi, p3811_1]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [hlam, p3811_0]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h3701, hlam, p3811_0]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                rcases p3811_3 (m.d 0 2) (by simp) with h3820 | h3820
                                · linarith only [h0, h3820, hlam]
                                · linarith only [h3661, h3820, hlam]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                rcases p3811_3 (m.d 0 2) (by simp) with h3823 | h3823
                                · linarith only [h0, h3823, hlam]
                                · linarith only [h3662, h3823, hlam]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                rcases p3811_3 (m.d 0 2) (by simp) with h3826 | h3826
                                · linarith only [h3826, hlam, p3811_0]
                                · rcases p3811_3 (m.d 1 2) (by simp) with h3828 | h3828
                                  · linarith only [h3701, h3828, hlam]
                                  · linarith only [h0, h3828, hlam]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3811_1]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [hlam, p3811_0]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                rcases p3811_3 (m.d 0 2) (by simp) with h3833 | h3833
                                · linarith only [h2808, h3833, hlam]
                                · linarith only [h3661, h3833, hlam]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                rcases p3811_3 (m.d 0 2) (by simp) with h3836 | h3836
                                · linarith only [h2808, h3836, hlam]
                                · linarith only [h3662, h3836, hlam]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h3661, hlam, p3811_0]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h3799, hlam, p3811_0]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h3805, hlam, p3811_1]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [hlam, p3811_0]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h3807, hlam, p3811_1]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h3662, hlam, p3811_0]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h3800, hlam, p3811_0]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h3806, hlam, p3811_1]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [h3662, h3805, hc34, hlam, hphi, ht0b, ht45, ht5b, p3811_1, u0elo1]
                              · have p3811_0 := h3811c.1
                                have p3811_1 := h3811c.2.1
                                have p3811_2 := h3811c.2.2.1
                                have p3811_3 := h3811c.2.2.2
                                linarith only [hlam, p3811_0]
                        · linarith only [h2808, h3664, h3806, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1991, h3701, h3800, h3803, h3805, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3664, h3701, h3802, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2494, h3663, h3701, h3800, h3801, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h3662, h3800, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h3661, h3799, hlam]
      · linarith only [h2808, h3662, h3664, hlam]
    · linarith only [h2808, h3661, h3663, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3857 | h3857
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3858 | h3858
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3859 | h3859
        · linarith only [h3661, h3662, h3859, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3861 | h3861
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3862 | h3862
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3863 | h3863
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3864 | h3864
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3865 | h3865
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3866 | h3866
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3867 | h3867
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3868 | h3868
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3869 | h3869
                          · linarith only [h3661, h3859, h3869, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3871 | h3871
                            · linarith only [h3661, h3662, h3867, h3869, h3871, hlam]
                            · rcases h2bigk with h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c | h3873c
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [hlam, p3873_0]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h0, hlam, p3873_1]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h2808, hlam, p3873_0]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3662, h3861, h3864, h3866, h3867, h3869, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3873_1]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3662, hlam, p3873_0]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                rcases p3873_3 (m.d 0 2) (by simp) with h3879 | h3879
                                · linarith only [h0, h3879, hlam]
                                · rcases p3873_3 (m.d 1 2) (by simp) with h3881 | h3881
                                  · rcases p3873_3 (m.d 2 3) (by simp) with h3882 | h3882
                                    · linarith only [h3861, h3882, hlam]
                                    · linarith only [h2808, h3882, hlam]
                                  · linarith only [h0, h3881, hlam]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [hlam, p3873_0]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h0, h3662, h3868, hc01, hc12, hlam, hphi, p3873_1]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3661, h3662, h3861, h3868, hlam, p3873_2]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3661, h3662, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3873_1]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3661, h3861, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3873_1]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3861, hlam, p3873_0]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [hlam, p3873_0]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                rcases p3873_3 (m.d 0 2) (by simp) with h3893 | h3893
                                · linarith only [h2808, h3893, hlam]
                                · linarith only [h3661, h3893, hlam]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3661, h3662, h3861, h3867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3873_1]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3661, hlam, p3873_0]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3862, hlam, p3873_0]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3867, hlam, p3873_1]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [hlam, p3873_0]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3869, hlam, p3873_1]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3661, h3863, h3867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3873_1]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3863, hlam, p3873_0]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [h3868, hlam, p3873_1]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                rcases p3873_3 (m.d 0 2) (by simp) with h3905 | h3905
                                · linarith only [h3662, h3905, hlam]
                                · linarith only [h3661, h3905, hlam]
                              · have p3873_0 := h3873c.1
                                have p3873_1 := h3873c.2.1
                                have p3873_2 := h3873c.2.2.1
                                have p3873_3 := h3873c.2.2.2
                                linarith only [hlam, p3873_0]
                        · linarith only [h3858, h3868, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2808, h3661, h3857, h3867, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3911 | h3911
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3912 | h3912
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3913 | h3913
                          · linarith only [h3661, h3866, h3913, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3915 | h3915
                            · linarith only [h3857, h3866, h3915, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                            · rcases h2bigk with h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c | h3917c
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [hlam, p3917_0]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h0, hlam, p3917_1]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h2808, hlam, p3917_0]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3662, h3858, hc24, hlam, hphi, ht0b, ht45, ht5b, p3917_1, u0elo2]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3662, hlam, p3917_0]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                rcases p3917_3 (m.d 0 2) (by simp) with h3923 | h3923
                                · linarith only [h0, h3923, hlam]
                                · rcases p3917_3 (m.d 1 2) (by simp) with h3925 | h3925
                                  · rcases p3917_3 (m.d 2 3) (by simp) with h3926 | h3926
                                    · linarith only [h3861, h3926, hlam]
                                    · linarith only [h2808, h3926, hlam]
                                  · linarith only [h0, h3925, hlam]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [hlam, p3917_0]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h0, h3662, h3912, hc01, hc12, hlam, hphi, p3917_1]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3661, h3662, h3861, h3912, hlam, p3917_2]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3661, h3662, h3911, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3917_1]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3661, h3861, h3911, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3917_1]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3861, hlam, p3917_0]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [hlam, p3917_0]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                rcases p3917_3 (m.d 0 2) (by simp) with h3937 | h3937
                                · linarith only [h2808, h3937, hlam]
                                · linarith only [h3661, h3937, hlam]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3661, h3662, h3861, h3911, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3917_1]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3661, hlam, p3917_0]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3862, hlam, p3917_0]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3911, hlam, p3917_1]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [hlam, p3917_0]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3913, hlam, p3917_1]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3661, h3863, h3911, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3917_1]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3863, hlam, p3917_0]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [h3912, hlam, p3917_1]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                rcases p3917_3 (m.d 0 2) (by simp) with h3949 | h3949
                                · linarith only [h3662, h3949, hlam]
                                · linarith only [h3661, h3949, hlam]
                              · have p3917_0 := h3917c.1
                                have p3917_1 := h3917c.2.1
                                have p3917_2 := h3917c.2.2.1
                                have p3917_3 := h3917c.2.2.2
                                linarith only [hlam, p3917_0]
                        · linarith only [h3858, h3912, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2808, h3857, h3911, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h3858, h3865, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2808, h3661, h3857, h3861, h3864, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h2808, h3661, h3861, h3863, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h2808, h3661, h3861, h3862, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3959 | h3959
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3960 | h3960
              · linarith only [h3661, h3662, h3861, h3960, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3962 | h3962
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3963 | h3963
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3964 | h3964
                    · linarith only [h1991, h3859, h3861, h3959, h3964, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3966 | h3966
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3967 | h3967
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3968 | h3968
                          · linarith only [h3661, h3964, h3968, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3970 | h3970
                            · linarith only [h0, h3960, h3968, h3970, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h2bigk with h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c | h3972c
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [hlam, p3972_0]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h0, hlam, p3972_1]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h2808, hlam, p3972_0]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3662, h3858, hc24, hlam, hphi, ht0b, ht45, ht5b, p3972_1, u0elo2]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3662, hlam, p3972_0]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3960, hc02, hc25, hlam, hphi, p3972_1]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [hlam, p3972_0]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3861, hlam, p3972_0]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3960, h3966, h3968, hc34, hc45, hlam, hphi, p3972_1]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3960, hlam, p3972_0]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                rcases p3972_3 (m.d 0 2) (by simp) with h3983 | h3983
                                · linarith only [h3983, hlam, p3972_0]
                                · rcases p3972_3 (m.d 1 2) (by simp) with h3985 | h3985
                                  · linarith only [h3861, h3985, hlam]
                                  · linarith only [h0, h3985, hlam]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3972_1]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [hlam, p3972_0]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                rcases p3972_3 (m.d 0 2) (by simp) with h3990 | h3990
                                · linarith only [h2808, h3990, hlam]
                                · linarith only [h3661, h3990, hlam]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3661, h3662, h3966, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3972_1]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3661, hlam, p3972_0]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3959, hlam, p3972_0]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3966, hlam, p3972_1]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [hlam, p3972_0]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3968, hlam, p3972_1]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3661, h3966, h3968, hc34, hc45, hlam, hphi, p3972_1]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h1991, h3959, hc01, hc25, hlam, hphi, ht12, p3972_1]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [h3967, hlam, p3972_1]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                rcases p3972_3 (m.d 0 2) (by simp) with h4002 | h4002
                                · linarith only [h3662, h4002, hlam]
                                · linarith only [h3661, h4002, hlam]
                              · have p3972_0 := h3972c.1
                                have p3972_1 := h3972c.2.1
                                have p3972_2 := h3972c.2.2.1
                                have p3972_3 := h3972c.2.2.2
                                linarith only [hlam, p3972_0]
                        · linarith only [h3858, h3967, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1991, h3861, h3959, h3966, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1991, h3858, h3861, h3959, h3963, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h1106, h3857, h3858, h3962, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
            · linarith only [h3661, h3959, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4011 | h4011
        · linarith only [h2808, h3661, h3858, h4011, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4013 | h4013
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4014 | h4014
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4015 | h4015
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4016 | h4016
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4017 | h4017
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4018 | h4018
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4019 | h4019
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4020 | h4020
                        · linarith only [h2808, h3661, h3858, h4013, h4020, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h2808, h3661, h4017, h4019, h4020, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h2808, h3661, h3857, h3858, h4019, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4024 | h4024
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4025 | h4025
                        · linarith only [h1106, h3858, h4013, h4025, hc01, hc12, hlam, hphi]
                        · linarith only [h2808, h3661, h4013, h4017, h4024, h4025, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h2808, h3661, h3857, h4024, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4029 | h4029
                    · linarith only [h1991, h4011, h4016, h4017, h4029, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4031 | h4031
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4032 | h4032
                        · linarith only [h1106, h4017, h4032, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4034 | h4034
                          · linarith only [h3661, h4029, h4034, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4036 | h4036
                            · linarith only [h2808, h3661, h4013, h4017, h4029, h4031, h4036, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h2808, h3661, h4013, h4017, h4031, h4036, hc34, hc45, hlam, hphi]
                      · linarith only [h2808, h3661, h3857, h3858, h4031, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                · linarith only [h2808, h3661, h3857, h4013, h4016, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h2808, h3661, h4013, h4015, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h2808, h3661, h4013, h4014, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4043 | h4043
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4044 | h4044
              · linarith only [h3661, h3662, h4013, h4044, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4046 | h4046
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4047 | h4047
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4048 | h4048
                    · linarith only [h1991, h4011, h4013, h4043, h4048, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4050 | h4050
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4051 | h4051
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4052 | h4052
                          · linarith only [h3661, h4048, h4052, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4054 | h4054
                            · linarith only [h1991, h4043, h4044, h4052, h4054, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h2bigk with h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [hlam, p4056_0]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h0, hlam, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h2808, hlam, p4056_0]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h2808, h3858, h4013, h4047, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h3662, hlam, p4056_0]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h4044, hc02, hc25, hlam, hphi, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [hlam, p4056_0]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h4013, hlam, p4056_0]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h4044, h4050, h4052, hc34, hc45, hlam, hphi, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h4044, hlam, p4056_0]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                rcases p4056_3 (m.d 0 2) (by simp) with h4067 | h4067
                                · linarith only [h4067, hlam, p4056_0]
                                · rcases p4056_3 (m.d 1 2) (by simp) with h4069 | h4069
                                  · linarith only [h4013, h4069, hlam]
                                  · linarith only [h0, h4069, hlam]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [hlam, p4056_0]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h2808, h3661, h3858, h4013, h4047, hlam, p4056_2]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h3661, h3662, h4050, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h3661, hlam, p4056_0]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h4043, hlam, p4056_0]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h4050, hlam, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [hlam, p4056_0]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h4052, hlam, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h3661, h4050, h4052, hc34, hc45, hlam, hphi, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h1991, h4043, hc01, hc25, hlam, hphi, ht12, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [h4051, hlam, p4056_1]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                rcases p4056_3 (m.d 0 2) (by simp) with h4084 | h4084
                                · linarith only [h3662, h4084, hlam]
                                · linarith only [h3661, h4084, hlam]
                              · have p4056_0 := h4056c.1
                                have p4056_1 := h4056c.2.1
                                have p4056_2 := h4056c.2.2.1
                                have p4056_3 := h4056c.2.2.2
                                linarith only [hlam, p4056_0]
                        · linarith only [h4013, h4047, h4051, hlam]
                      · linarith only [h3858, h4013, h4047, h4050, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4090 | h4090
                    · linarith only [h1991, h4011, h4013, h4043, h4090, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4092 | h4092
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4093 | h4093
                        · linarith only [h0, h4013, h4047, h4093, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h1991, h4013, h4043, h4093, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1991, h4013, h4043, h4092, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1991, h3857, h4013, h4043, h4046, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h3661, h4043, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
    · linarith only [h2808, h3661, h3857, hlam]

end R2N4
