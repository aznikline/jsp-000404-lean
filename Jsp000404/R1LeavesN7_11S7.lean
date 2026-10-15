import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9616000 in
set_option maxHeartbeats 9616000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s7_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h3620 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 5 (by decide) (by decide) with h3621 | h3621
  · rcases m.htr 1 3 4 (by decide) (by decide) with h3622 | h3622
    · rcases m.htr 1 3 5 (by decide) (by decide) with h3623 | h3623
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3624 | h3624
        · linarith only [h3624, h8, hc14, hlam, hphi, ht01, u0ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h3626 | h3626
          · rcases m.htr 2 3 5 (by decide) (by decide) with h3627 | h3627
            · rcases m.htr 2 4 5 (by decide) (by decide) with h3628 | h3628
              · linarith only [h3626, h3628, h8, hc23, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h3630 | h3630
                · linarith only [h3621, h3626, h3628, h3630, h8, hc15, hlam, hphi, ht01, u0ehi3]
                · rcases h2bigk with h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c | h3632c
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h0, h3620, h3627, h3630, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3632_1]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    rcases p3632_3 (m.d 0 2) (by simp) with h3635 | h3635
                    · rcases p3632_3 (m.d 1 2) (by simp) with h3636 | h3636
                      · linarith only [h0, h3636, hlam]
                      · linarith only [h3620, h3636, hlam]
                    · linarith only [h3635, hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    rcases p3632_3 (m.d 0 2) (by simp) with h3640 | h3640
                    · rcases p3632_3 (m.d 1 2) (by simp) with h3641 | h3641
                      · linarith only [h0, h3641, hlam]
                      · linarith only [h3620, h3627, h3628, h3641, hlam]
                    · linarith only [h3640, hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    rcases p3632_3 (m.d 0 2) (by simp) with h3645 | h3645
                    · rcases p3632_3 (m.d 1 2) (by simp) with h3646 | h3646
                      · linarith only [h0, h3646, hlam]
                      · linarith only [h3621, h3646, hlam]
                    · linarith only [h3645, hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h0, hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h0, h3627, h3630, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3632_1]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    rcases p3632_3 (m.d 0 2) (by simp) with h3653 | h3653
                    · rcases p3632_3 (m.d 1 2) (by simp) with h3654 | h3654
                      · rcases p3632_3 (m.d 2 3) (by simp) with h3655 | h3655
                        · linarith only [h3620, h3655, hlam]
                        · linarith only [h3626, h3655, hlam]
                      · linarith only [h3654, hlam, p3632_0]
                    · linarith only [h3653, h4, hlam]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    rcases p3632_3 (m.d 0 2) (by simp) with h3660 | h3660
                    · rcases p3632_3 (m.d 1 2) (by simp) with h3661 | h3661
                      · rcases p3632_3 (m.d 2 3) (by simp) with h3662 | h3662
                        · linarith only [h3620, h3662, hlam]
                        · linarith only [h3627, h3662, hlam]
                      · linarith only [h3661, hlam, p3632_0]
                    · linarith only [h3660, h5, hlam]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h3, hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h3620, hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h0, h3620, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3632_1]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h0, h3620, hc01, hc25, hlam, hphi, ht0b, ht5b, p3632_1]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h4, hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h0, h3620, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3632_1]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h3626, hlam, p3632_1]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h3628, hlam, p3632_1]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h5, hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h3621, hlam, p3632_0]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h3627, hlam, p3632_1]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [h0, h3621, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3632_1]
                  · have p3632_0 := h3632c.1
                    have p3632_1 := h3632c.2.1
                    have p3632_2 := h3632c.2.2.1
                    have p3632_3 := h3632c.2.2.2
                    linarith only [hlam, p3632_0]
            · linarith only [h0, h3620, h3623, h3626, h3627, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h3683 | h3683
            · linarith only [h0, h3620, h3622, h3626, h3683, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h3685 | h3685
              · linarith only [h3685, h8, hc24, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h3687 | h3687
                · linarith only [h0, h3620, h3622, h3687, h8, hc01, hlam, hphi, u0ehi3]
                · rcases h2bigk with h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c | h3689c
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h0, h3620, h3623, h3626, h3687, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3689_1]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    rcases p3689_3 (m.d 0 2) (by simp) with h3692 | h3692
                    · rcases p3689_3 (m.d 1 2) (by simp) with h3693 | h3693
                      · linarith only [h0, h3693, hlam]
                      · linarith only [h3620, h3693, hlam]
                    · linarith only [h3692, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    rcases p3689_3 (m.d 0 2) (by simp) with h3697 | h3697
                    · rcases p3689_3 (m.d 1 2) (by simp) with h3698 | h3698
                      · linarith only [h0, h3698, hlam]
                      · linarith only [h3620, h3623, h3683, h3685, h3698, hlam]
                    · linarith only [h3697, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    rcases p3689_3 (m.d 0 2) (by simp) with h3702 | h3702
                    · rcases p3689_3 (m.d 1 2) (by simp) with h3703 | h3703
                      · linarith only [h0, h3703, hlam]
                      · linarith only [h3621, h3703, hlam]
                    · linarith only [h3702, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h0, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    rcases p3689_3 (m.d 0 2) (by simp) with h3709 | h3709
                    · rcases p3689_3 (m.d 1 2) (by simp) with h3710 | h3710
                      · rcases p3689_3 (m.d 2 3) (by simp) with h3711 | h3711
                        · linarith only [h3711, hlam, p3689_0]
                        · rcases p3689_3 (m.d 2 4) (by simp) with h3713 | h3713
                          · linarith only [h3620, h3623, h3626, h3687, h3713, h4, h8, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h3626, h3713, hlam]
                      · linarith only [h3710, hlam, p3689_0]
                    · linarith only [h3, h3709, hlam]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    rcases p3689_3 (m.d 0 2) (by simp) with h3718 | h3718
                    · rcases p3689_3 (m.d 1 2) (by simp) with h3719 | h3719
                      · rcases p3689_3 (m.d 2 3) (by simp) with h3720 | h3720
                        · linarith only [h3620, h3720, hlam]
                        · rcases p3689_3 (m.d 2 4) (by simp) with h3722 | h3722
                          · linarith only [h3722, hlam, p3689_0]
                          · rcases p3689_3 (m.d 2 5) (by simp) with h3724 | h3724
                            · linarith only [h3621, h3724, hlam]
                            · linarith only [h3685, h3724, hlam]
                      · linarith only [h3719, hlam, p3689_0]
                    · linarith only [h3718, h4, hlam]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    rcases p3689_3 (m.d 0 2) (by simp) with h3729 | h3729
                    · rcases p3689_3 (m.d 1 2) (by simp) with h3730 | h3730
                      · rcases p3689_3 (m.d 2 3) (by simp) with h3731 | h3731
                        · linarith only [h3620, h3731, hlam]
                        · rcases p3689_3 (m.d 2 4) (by simp) with h3733 | h3733
                          · linarith only [h3685, h3733, hlam, p3689_1]
                          · rcases p3689_3 (m.d 2 5) (by simp) with h3735 | h3735
                            · linarith only [h3735, hlam, p3689_0]
                            · rcases h3bigk with h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c | h3737c
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h0, h3, h3622, h3626, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3737_1]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                rcases p3737_3 (m.d 0 3) (by simp) with h3740 | h3740
                                · rcases p3737_3 (m.d 1 3) (by simp) with h3741 | h3741
                                  · linarith only [h1, h3741, hlam]
                                  · linarith only [h3620, h3741, hlam]
                                · linarith only [h3, h3740, hlam]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                rcases p3737_3 (m.d 0 3) (by simp) with h3745 | h3745
                                · rcases p3737_3 (m.d 1 3) (by simp) with h3746 | h3746
                                  · linarith only [h1, h3746, hlam]
                                  · linarith only [h3622, h3746, hlam]
                                · linarith only [h3745, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                rcases p3737_3 (m.d 0 3) (by simp) with h3750 | h3750
                                · rcases p3737_3 (m.d 1 3) (by simp) with h3751 | h3751
                                  · linarith only [h1, h3751, hlam]
                                  · linarith only [h3623, h3751, hlam]
                                · linarith only [h3750, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h1, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                rcases p3737_3 (m.d 0 3) (by simp) with h3757 | h3757
                                · rcases p3737_3 (m.d 1 3) (by simp) with h3758 | h3758
                                  · rcases p3737_3 (m.d 2 3) (by simp) with h3759 | h3759
                                    · linarith only [h3620, h3759, hlam]
                                    · rcases p3737_3 (m.d 3 4) (by simp) with h3761 | h3761
                                      · linarith only [h3622, h3761, hlam]
                                      · linarith only [h3626, h3761, hlam]
                                  · linarith only [h3620, h3758, hlam]
                                · linarith only [h3, h3757, hlam]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h0, h3620, h3626, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3737_1]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h0, h3620, h3683, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3737_1]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h3, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h3620, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h3626, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h3683, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h6, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h3622, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h6, h8, hc23, hc45, hlam, hphi, ht34, p3737_1]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h3687, hlam, p3737_1]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h7, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h3623, hlam, p3737_0]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h0, h3620, h3623, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3737_1]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [h0, h3620, h3623, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3737_1]
                              · have p3737_0 := h3737c.1
                                have p3737_1 := h3737c.2.1
                                have p3737_2 := h3737c.2.2.1
                                have p3737_3 := h3737c.2.2.2
                                linarith only [hlam, p3737_0]
                      · linarith only [h3730, hlam, p3689_0]
                    · linarith only [h3729, h5, hlam]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h3, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h3620, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h3626, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h3683, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h4, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3689_1]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h0, h3620, h3622, h3626, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3689_1]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h3685, hlam, p3689_1]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h5, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h3621, hlam, p3689_0]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h0, h3620, h3623, h3683, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3689_1]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [h0, h3620, h3623, h3683, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3689_1]
                  · have p3689_0 := h3689c.1
                    have p3689_1 := h3689c.2.1
                    have p3689_2 := h3689c.2.2.1
                    have p3689_3 := h3689c.2.2.2
                    linarith only [hlam, p3689_0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3800 | h3800
        · linarith only [h3800, h8, hc14, hlam, hphi, ht01, u0ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h3802 | h3802
          · rcases m.htr 2 3 5 (by decide) (by decide) with h3803 | h3803
            · linarith only [h3620, h3623, h3803, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h3805 | h3805
              · linarith only [h3805, h8, hc24, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h3807 | h3807
                · linarith only [h0, h3, h3620, h3623, h3802, h3807, h7, h8, hc01, hlam, hphi, u0ehi3]
                · rcases h2bigk with h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c | h3809c
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h0, h3621, h3802, h3803, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3809_1]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    rcases p3809_3 (m.d 0 2) (by simp) with h3812 | h3812
                    · rcases p3809_3 (m.d 1 2) (by simp) with h3813 | h3813
                      · linarith only [h0, h3813, hlam]
                      · linarith only [h3620, h3813, hlam]
                    · linarith only [h3812, hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    rcases p3809_3 (m.d 0 2) (by simp) with h3817 | h3817
                    · rcases p3809_3 (m.d 1 2) (by simp) with h3818 | h3818
                      · linarith only [h0, h3818, hlam]
                      · linarith only [h3621, h3802, h3803, h3818, hlam]
                    · linarith only [h3817, hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    rcases p3809_3 (m.d 0 2) (by simp) with h3822 | h3822
                    · rcases p3809_3 (m.d 1 2) (by simp) with h3823 | h3823
                      · linarith only [h0, h3823, hlam]
                      · linarith only [h3621, h3823, hlam]
                    · linarith only [h3822, hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h0, hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h0, h3802, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3809_1]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    rcases p3809_3 (m.d 0 2) (by simp) with h3830 | h3830
                    · rcases p3809_3 (m.d 1 2) (by simp) with h3831 | h3831
                      · rcases p3809_3 (m.d 2 3) (by simp) with h3832 | h3832
                        · linarith only [h3620, h3832, hlam]
                        · linarith only [h3802, h3832, hlam]
                      · linarith only [h3831, hlam, p3809_0]
                    · linarith only [h3830, h4, hlam]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h0, h3802, h3803, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3809_1]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h3, hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h3620, hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h0, h3620, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3809_1]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h3803, hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h4, hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3809_1]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h3802, hlam, p3809_1]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h3805, hlam, p3809_1]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h5, hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h3621, hlam, p3809_0]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h0, h3621, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3809_1]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [h0, h3621, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3809_1]
                  · have p3809_0 := h3809c.1
                    have p3809_1 := h3809c.2.1
                    have p3809_2 := h3809c.2.2.1
                    have p3809_3 := h3809c.2.2.2
                    linarith only [hlam, p3809_0]
          · linarith only [h0, h3, h3622, h3623, h3802, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h3854 | h3854
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3855 | h3855
        · linarith only [h3622, h3854, h3855, h6, h8, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
        · linarith only [h3622, h3854, h3855, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3858 | h3858
        · linarith only [h3858, h8, hc14, hlam, hphi, ht01, u0ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h3860 | h3860
          · linarith only [h3620, h3622, h3860, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h3862 | h3862
            · linarith only [h3620, h3854, h3862, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h3864 | h3864
              · linarith only [h3864, h8, hc24, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h3866 | h3866
                · linarith only [h3866, h8, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                · rcases h2bigk with h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    rcases p3868_3 (m.d 0 2) (by simp) with h3870 | h3870
                    · rcases p3868_3 (m.d 1 2) (by simp) with h3871 | h3871
                      · linarith only [h0, h3871, hlam]
                      · rcases p3868_3 (m.d 2 3) (by simp) with h3873 | h3873
                        · linarith only [h3, h3873, hlam]
                        · rcases p3868_3 (m.d 2 4) (by simp) with h3875 | h3875
                          · linarith only [h3875, h4, hlam]
                          · rcases p3868_3 (m.d 2 5) (by simp) with h3877 | h3877
                            · linarith only [h3877, h5, hlam]
                            · rcases h3bigk with h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                rcases p3879_3 (m.d 0 3) (by simp) with h3881 | h3881
                                · rcases p3879_3 (m.d 1 3) (by simp) with h3882 | h3882
                                  · linarith only [h1, h3882, hlam]
                                  · rcases p3879_3 (m.d 2 3) (by simp) with h3884 | h3884
                                    · linarith only [h3, h3884, hlam]
                                    · rcases p3879_3 (m.d 3 4) (by simp) with h3886 | h3886
                                      · linarith only [h3886, h6, hlam]
                                      · linarith only [h3622, h3886, hlam]
                                · linarith only [h1, h3881, hlam]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                rcases p3879_3 (m.d 0 3) (by simp) with h3890 | h3890
                                · rcases p3879_3 (m.d 1 3) (by simp) with h3891 | h3891
                                  · linarith only [h1, h3891, hlam]
                                  · linarith only [h3620, h3891, hlam]
                                · linarith only [h3, h3890, hlam]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                rcases p3879_3 (m.d 0 3) (by simp) with h3895 | h3895
                                · rcases p3879_3 (m.d 1 3) (by simp) with h3896 | h3896
                                  · linarith only [h1, h3896, hlam]
                                  · rcases p3879_3 (m.d 2 3) (by simp) with h3898 | h3898
                                    · linarith only [h3, h3898, hlam]
                                    · rcases p3879_3 (m.d 3 4) (by simp) with h3900 | h3900
                                      · linarith only [h3900, hlam, p3879_0]
                                      · rcases p3879_3 (m.d 3 5) (by simp) with h3902 | h3902
                                        · linarith only [h3902, h7, hlam]
                                        · linarith only [h3866, h3902, hlam]
                                · linarith only [h3895, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                rcases p3879_3 (m.d 0 3) (by simp) with h3906 | h3906
                                · rcases p3879_3 (m.d 1 3) (by simp) with h3907 | h3907
                                  · linarith only [h1, h3907, hlam]
                                  · rcases p3879_3 (m.d 2 3) (by simp) with h3909 | h3909
                                    · linarith only [h3, h3909, hlam]
                                    · rcases p3879_3 (m.d 3 4) (by simp) with h3911 | h3911
                                      · linarith only [h3911, h6, hlam]
                                      · rcases p3879_3 (m.d 3 5) (by simp) with h3913 | h3913
                                        · linarith only [h3913, hlam, p3879_0]
                                        · rcases h5bigk with h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [hlam, p3915_0]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3620, h3622, h3858, h8, hc23, hc45, hlam, hphi, ht34, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3860, h3864, h8, hc23, hc45, hlam, hphi, ht34, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3620, h3622, h3866, h8, hc23, hc45, hlam, hphi, ht34, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h8, hlam, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h2, hlam, p3915_0]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [hlam, p3915_0]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h2, h3860, h3864, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3854, hlam, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3858, hlam, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h5, hlam, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3621, hlam, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [hlam, p3915_0]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3862, hlam, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3864, hlam, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h7, hlam, p3915_0]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [hc03, hc15, hlam, hphi, ht0b, ht5b, p3879_1, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h0, h3, h3860, h3864, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3879_1, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [hlam, p3915_0]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3866, hlam, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p3915_1, u0ehi4]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3621, h3860, h3864, hc23, hc45, hlam, hphi, ht34, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3860, h3864, hc23, hc45, hlam, hphi, ht34, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [h3620, h3854, hc23, hc45, hlam, hphi, ht34, p3915_1]
                                          · have p3915_0 := h3915c.1
                                            have p3915_1 := h3915c.2.1
                                            have p3915_2 := h3915c.2.2.1
                                            have p3915_3 := h3915c.2.2.2
                                            linarith only [hlam, p3915_0]
                                · linarith only [h3906, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h1, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h3622, hc23, hc34, hlam, hphi, p3879_1]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h3622, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h3854, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h3, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h3620, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h3860, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h3862, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h6, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h6, h8, hc13, hc45, hlam, hphi, ht34, p3879_1]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h6, h8, hc23, hc45, hlam, hphi, ht34, p3879_1]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h3866, hlam, p3879_1]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h7, hlam, p3879_0]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                rcases p3879_3 (m.d 0 3) (by simp) with h3958 | h3958
                                · rcases p3879_3 (m.d 1 3) (by simp) with h3959 | h3959
                                  · linarith only [h3959, hlam, p3879_0]
                                  · rcases p3879_3 (m.d 2 3) (by simp) with h3961 | h3961
                                    · linarith only [h3862, h3961, hlam]
                                    · rcases p3879_3 (m.d 3 4) (by simp) with h3963 | h3963
                                      · linarith only [h3866, h3963, hlam]
                                      · linarith only [h3622, h3963, hlam]
                                · linarith only [h1, h3958, hlam]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                rcases p3879_3 (m.d 0 3) (by simp) with h3967 | h3967
                                · rcases p3879_3 (m.d 1 3) (by simp) with h3968 | h3968
                                  · linarith only [h3854, h3968, hlam]
                                  · linarith only [h3620, h3968, hlam]
                                · linarith only [h3, h3967, hlam]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [h3620, h3622, hc23, hc35, hlam, hphi, p3879_1]
                              · have p3879_0 := h3879c.1
                                have p3879_1 := h3879c.2.1
                                have p3879_2 := h3879c.2.2.1
                                have p3879_3 := h3879c.2.2.2
                                linarith only [hlam, p3879_0]
                    · linarith only [h0, h3870, hlam]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    rcases p3868_3 (m.d 0 2) (by simp) with h3975 | h3975
                    · rcases p3868_3 (m.d 1 2) (by simp) with h3976 | h3976
                      · linarith only [h0, h3976, hlam]
                      · linarith only [h3620, h3976, hlam]
                    · linarith only [h3975, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    rcases p3868_3 (m.d 0 2) (by simp) with h3980 | h3980
                    · rcases p3868_3 (m.d 1 2) (by simp) with h3981 | h3981
                      · linarith only [h0, h3981, hlam]
                      · linarith only [h3621, h3864, h3981, hlam]
                    · linarith only [h3980, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    rcases p3868_3 (m.d 0 2) (by simp) with h3985 | h3985
                    · rcases p3868_3 (m.d 1 2) (by simp) with h3986 | h3986
                      · linarith only [h0, h3986, hlam]
                      · linarith only [h3621, h3986, hlam]
                    · linarith only [h3985, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h0, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    rcases p3868_3 (m.d 0 2) (by simp) with h3992 | h3992
                    · rcases p3868_3 (m.d 1 2) (by simp) with h3993 | h3993
                      · rcases p3868_3 (m.d 2 3) (by simp) with h3994 | h3994
                        · linarith only [h3994, hlam, p3868_0]
                        · rcases p3868_3 (m.d 2 4) (by simp) with h3996 | h3996
                          · linarith only [h3996, h4, h8, hc23, hc45, hlam, hphi, ht34, p3868_1]
                          · linarith only [h3860, h3996, hlam]
                      · linarith only [h3993, hlam, p3868_0]
                    · linarith only [h3, h3992, hlam]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    rcases p3868_3 (m.d 0 2) (by simp) with h4001 | h4001
                    · rcases p3868_3 (m.d 1 2) (by simp) with h4002 | h4002
                      · rcases p3868_3 (m.d 2 3) (by simp) with h4003 | h4003
                        · linarith only [h3620, h4003, hlam]
                        · rcases p3868_3 (m.d 2 4) (by simp) with h4005 | h4005
                          · linarith only [h4005, hlam, p3868_0]
                          · rcases p3868_3 (m.d 2 5) (by simp) with h4007 | h4007
                            · linarith only [h3621, h4007, hlam]
                            · linarith only [h3864, h4007, hlam]
                      · linarith only [h4002, hlam, p3868_0]
                    · linarith only [h4, h4001, hlam]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    rcases p3868_3 (m.d 0 2) (by simp) with h4012 | h4012
                    · rcases p3868_3 (m.d 1 2) (by simp) with h4013 | h4013
                      · rcases p3868_3 (m.d 2 3) (by simp) with h4014 | h4014
                        · linarith only [h3620, h4014, hlam]
                        · rcases p3868_3 (m.d 2 4) (by simp) with h4016 | h4016
                          · linarith only [h3864, h4016, hlam, p3868_1]
                          · rcases p3868_3 (m.d 2 5) (by simp) with h4018 | h4018
                            · linarith only [h4018, hlam, p3868_0]
                            · rcases h3bigk with h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c | h4020c
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                rcases p4020_3 (m.d 0 3) (by simp) with h4022 | h4022
                                · rcases p4020_3 (m.d 1 3) (by simp) with h4023 | h4023
                                  · linarith only [h1, h4023, hlam]
                                  · rcases p4020_3 (m.d 2 3) (by simp) with h4025 | h4025
                                    · linarith only [h3, h4025, hlam]
                                    · rcases p4020_3 (m.d 3 4) (by simp) with h4027 | h4027
                                      · linarith only [h4027, h6, hlam]
                                      · linarith only [h3622, h4027, hlam]
                                · linarith only [h1, h4022, hlam]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                rcases p4020_3 (m.d 0 3) (by simp) with h4031 | h4031
                                · rcases p4020_3 (m.d 1 3) (by simp) with h4032 | h4032
                                  · linarith only [h1, h4032, hlam]
                                  · linarith only [h3620, h4032, hlam]
                                · linarith only [h3, h4031, hlam]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                rcases p4020_3 (m.d 0 3) (by simp) with h4036 | h4036
                                · rcases p4020_3 (m.d 1 3) (by simp) with h4037 | h4037
                                  · linarith only [h1, h4037, hlam]
                                  · rcases p4020_3 (m.d 2 3) (by simp) with h4039 | h4039
                                    · linarith only [h3, h4039, hlam]
                                    · rcases p4020_3 (m.d 3 4) (by simp) with h4041 | h4041
                                      · linarith only [h4041, hlam, p4020_0]
                                      · rcases p4020_3 (m.d 3 5) (by simp) with h4043 | h4043
                                        · linarith only [h4043, h7, hlam]
                                        · linarith only [h3866, h4043, hlam]
                                · linarith only [h4036, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                rcases p4020_3 (m.d 0 3) (by simp) with h4047 | h4047
                                · rcases p4020_3 (m.d 1 3) (by simp) with h4048 | h4048
                                  · linarith only [h1, h4048, hlam]
                                  · rcases p4020_3 (m.d 2 3) (by simp) with h4050 | h4050
                                    · linarith only [h3, h4050, hlam]
                                    · rcases p4020_3 (m.d 3 4) (by simp) with h4052 | h4052
                                      · linarith only [h4052, h6, hlam]
                                      · rcases p4020_3 (m.d 3 5) (by simp) with h4054 | h4054
                                        · linarith only [h4054, hlam, p4020_0]
                                        · rcases h5bigk with h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [hlam, p4056_0]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3621, h3864, h8, hc24, hc45, hlam, hphi, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3864, h8, hc24, hc45, hlam, hphi, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3620, h3622, h3866, h8, hc23, hc45, hlam, hphi, ht34, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h8, hlam, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h2, hlam, p4056_0]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [hlam, p4056_0]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h2, h3864, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3854, hlam, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3858, hlam, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h5, hlam, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3621, hlam, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [hlam, p4056_0]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3862, hlam, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3864, hlam, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h7, hlam, p4056_0]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p4020_1, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h0, h3, h3860, h3864, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4020_1, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [hlam, p4056_0]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3866, hlam, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p4056_1, u0ehi4]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3620, h3622, h3858, hc23, hc45, hlam, hphi, ht34, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3860, h3864, hc23, hc45, hlam, hphi, ht34, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [h3620, h3622, h3866, hc23, hc45, hlam, hphi, ht34, p4056_1]
                                          · have p4056_0 := h4056c.1
                                            have p4056_1 := h4056c.2.1
                                            have p4056_2 := h4056c.2.2.1
                                            have p4056_3 := h4056c.2.2.2
                                            linarith only [hlam, p4056_0]
                                · linarith only [h4047, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h1, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h3622, hc23, hc34, hlam, hphi, p4020_1]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h3622, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h3854, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h3, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h3620, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h3860, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h3862, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h6, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h6, h8, hc13, hc45, hlam, hphi, ht34, p4020_1]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h6, h8, hc23, hc45, hlam, hphi, ht34, p4020_1]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h3866, hlam, p4020_1]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h7, hlam, p4020_0]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                rcases p4020_3 (m.d 0 3) (by simp) with h4099 | h4099
                                · rcases p4020_3 (m.d 1 3) (by simp) with h4100 | h4100
                                  · linarith only [h4100, hlam, p4020_0]
                                  · rcases p4020_3 (m.d 2 3) (by simp) with h4102 | h4102
                                    · linarith only [h3862, h4102, hlam]
                                    · rcases p4020_3 (m.d 3 4) (by simp) with h4104 | h4104
                                      · linarith only [h3866, h4104, hlam]
                                      · linarith only [h3622, h4104, hlam]
                                · linarith only [h1, h4099, hlam]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                rcases p4020_3 (m.d 0 3) (by simp) with h4108 | h4108
                                · rcases p4020_3 (m.d 1 3) (by simp) with h4109 | h4109
                                  · linarith only [h3854, h4109, hlam]
                                  · linarith only [h3620, h4109, hlam]
                                · linarith only [h3, h4108, hlam]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [h0, h3, h3620, h3622, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4020_1]
                              · have p4020_0 := h4020c.1
                                have p4020_1 := h4020c.2.1
                                have p4020_2 := h4020c.2.2.1
                                have p4020_3 := h4020c.2.2.2
                                linarith only [hlam, p4020_0]
                      · linarith only [h4013, hlam, p3868_0]
                    · linarith only [h4012, h5, hlam]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h3, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h3620, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h3860, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h3862, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h4, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3868_1]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h0, h3621, h3864, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3868_1]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h3864, hlam, p3868_1]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h5, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h3621, hlam, p3868_0]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h0, h3621, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3868_1]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [h0, h3621, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3868_1]
                  · have p3868_0 := h3868c.1
                    have p3868_1 := h3868c.2.1
                    have p3868_2 := h3868c.2.2.1
                    have p3868_3 := h3868c.2.2.2
                    linarith only [hlam, p3868_0]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h4132 | h4132
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4133 | h4133
      · linarith only [h3620, h3621, h4133, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4135 | h4135
        · linarith only [h4135, h8, hc14, hlam, hphi, ht01, u0ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4137 | h4137
          · linarith only [h0, h3620, h3621, h4137, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h3, h4132, h4133, h4137, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4140 | h4140
      · linarith only [h3620, h3621, h4132, h4140, h6, h8, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4142 | h4142
        · linarith only [h4142, h8, hc14, hlam, hphi, ht01, u0ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4144 | h4144
          · linarith only [h0, h3620, h4132, h4144, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h4146 | h4146
            · linarith only [h0, h3620, h3621, h4140, h4146, h5, hc01, hc15, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h4148 | h4148
              · linarith only [h4148, h8, hc24, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h4150 | h4150
                · linarith only [h4150, h6, h8, hlam]
                · rcases h2bigk with h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c | h4152c
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    rcases p4152_3 (m.d 0 2) (by simp) with h4154 | h4154
                    · rcases p4152_3 (m.d 1 2) (by simp) with h4155 | h4155
                      · linarith only [h0, h4155, hlam]
                      · rcases p4152_3 (m.d 2 3) (by simp) with h4157 | h4157
                        · linarith only [h3, h4157, hlam]
                        · rcases p4152_3 (m.d 2 4) (by simp) with h4159 | h4159
                          · linarith only [h4, h4159, hlam]
                          · rcases p4152_3 (m.d 2 5) (by simp) with h4161 | h4161
                            · linarith only [h4161, h5, hlam]
                            · linarith only [h3621, h4161, hlam]
                    · linarith only [h0, h4154, hlam]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h3, h3620, h3621, h4146, h7, hlam, p4152_2]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    rcases p4152_3 (m.d 0 2) (by simp) with h4166 | h4166
                    · rcases p4152_3 (m.d 1 2) (by simp) with h4167 | h4167
                      · linarith only [h0, h4167, hlam]
                      · rcases p4152_3 (m.d 2 3) (by simp) with h4169 | h4169
                        · linarith only [h3, h4169, hlam]
                        · rcases p4152_3 (m.d 2 4) (by simp) with h4171 | h4171
                          · linarith only [h4171, hlam, p4152_0]
                          · rcases p4152_3 (m.d 2 5) (by simp) with h4173 | h4173
                            · linarith only [h4173, h5, hlam]
                            · linarith only [h4148, h4173, hlam]
                    · linarith only [h4166, hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h0, h3620, h3621, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4152_1]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h0, hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h0, h3621, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4152_1]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h0, h3, h3621, h4146, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4152_1]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h3621, hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h3, hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h3620, hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h4144, hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h4146, hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h4, hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4152_1]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h4144, h6, h8, hc23, hc45, hlam, hphi, ht34, p4152_1]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h4148, hlam, p4152_1]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h5, hlam, p4152_0]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [h0, h3, h3620, h4146, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4152_1]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    rcases p4152_3 (m.d 0 2) (by simp) with h4195 | h4195
                    · rcases p4152_3 (m.d 1 2) (by simp) with h4196 | h4196
                      · linarith only [h3621, h4196, hlam]
                      · linarith only [h3620, h4196, hlam]
                    · linarith only [h3, h4195, hlam]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    rcases p4152_3 (m.d 0 2) (by simp) with h4200 | h4200
                    · rcases p4152_3 (m.d 1 2) (by simp) with h4201 | h4201
                      · linarith only [h3621, h4201, hlam]
                      · linarith only [h0, h3, h3620, h4146, h4201, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4152_1]
                    · linarith only [h4, h4200, hlam]
                  · have p4152_0 := h4152c.1
                    have p4152_1 := h4152c.2.1
                    have p4152_2 := h4152c.2.2.1
                    have p4152_3 := h4152c.2.2.2
                    linarith only [hlam, p4152_0]

end R2N4
