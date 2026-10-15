import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_33S9
import Jsp000404.R1LeavesN7_33S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3426 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3671 | h3671
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3672 | h3672
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3673 | h3673
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3674 | h3674
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3675 | h3675
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3676 | h3676
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3677 | h3677
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3678 | h3678
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3679 | h3679
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3680 | h3680
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3681 | h3681
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3682 | h3682
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3683 | h3683
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3684 | h3684
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3685 | h3685
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3686 | h3686
                                · linarith only [h3671, h3683, h3686, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · linarith only [h0, h3671, h3683, h3685, h3686, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3689 | h3689
                                · linarith only [h0, h3671, h3674, h3685, h3689, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases h2bigk with h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c | h3691c
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h0, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h0, h3684, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p3691_1, u2elo1]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    rcases p3691_3 (m.d 0 2) (by simp) with h3695 | h3695
                                    · rcases p3691_3 (m.d 1 2) (by simp) with h3696 | h3696
                                      · rcases p3691_3 (m.d 2 3) (by simp) with h3697 | h3697
                                        · linarith only [h3671, h3697, hlam]
                                        · linarith only [h3683, h3697, hlam]
                                      · linarith only [h3678, h3696, hlam]
                                    · linarith only [h3695, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    rcases p3691_3 (m.d 0 2) (by simp) with h3702 | h3702
                                    · rcases p3691_3 (m.d 1 2) (by simp) with h3703 | h3703
                                      · rcases p3691_3 (m.d 2 3) (by simp) with h3704 | h3704
                                        · linarith only [h3671, h3704, hlam]
                                        · linarith only [h3684, h3704, hlam]
                                      · linarith only [h3679, h3703, hlam]
                                    · linarith only [h3702, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3691_1, u2elo1]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3684, h3689, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3691_1, u2elo1]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    rcases p3691_3 (m.d 0 2) (by simp) with h3712 | h3712
                                    · linarith only [h0, h3712, hlam]
                                    · linarith only [h3672, h3712, hlam]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    rcases p3691_3 (m.d 0 2) (by simp) with h3715 | h3715
                                    · linarith only [h0, h3715, hlam]
                                    · linarith only [h3673, h3715, hlam]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3671, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3677, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3671, h3683, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3691_1, u2elo0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h0, h3671, h3684, h3689, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3691_1, u2elo1]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3672, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3678, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3683, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3685, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3673, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3679, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h3684, hlam, p3691_0]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [h0, h3673, h3683, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3691_1, u2elo1]
                                  · have p3691_0 := h3691c.1
                                    have p3691_1 := h3691c.2.1
                                    have p3691_2 := h3691c.2.2.1
                                    have p3691_3 := h3691c.2.2.2
                                    linarith only [hlam, p3691_0]
                            · linarith only [h2314, h3675, h3677, h3683, h3684, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3734 | h3734
                            · linarith only [h2314, h3674, h3677, h3683, h3734, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3736 | h3736
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3737 | h3737
                                · rcases h2bigk with h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c | h3738c
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h0, hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    rcases p3738_3 (m.d 0 2) (by simp) with h3741 | h3741
                                    · rcases p3738_3 (m.d 1 2) (by simp) with h3742 | h3742
                                      · rcases p3738_3 (m.d 2 3) (by simp) with h3743 | h3743
                                        · linarith only [h3743, hlam, p3738_0]
                                        · rcases p3738_3 (m.d 2 4) (by simp) with h3745 | h3745
                                          · linarith only [h3672, h3745, hlam]
                                          · linarith only [h3683, h3745, hlam]
                                      · linarith only [h3677, h3742, hlam]
                                    · linarith only [h3741, hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h0, h3736, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3738_1, u2elo1]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    rcases p3738_3 (m.d 0 2) (by simp) with h3751 | h3751
                                    · rcases p3738_3 (m.d 1 2) (by simp) with h3752 | h3752
                                      · rcases p3738_3 (m.d 2 3) (by simp) with h3753 | h3753
                                        · linarith only [h3671, h3753, hlam]
                                        · rcases p3738_3 (m.d 2 4) (by simp) with h3755 | h3755
                                          · linarith only [h3672, h3755, hlam]
                                          · linarith only [h3736, h3755, hlam]
                                      · linarith only [h3679, h3752, hlam]
                                    · linarith only [h3751, hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3738_1, u2elo1]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    rcases p3738_3 (m.d 0 2) (by simp) with h3762 | h3762
                                    · linarith only [h0, h3762, hlam]
                                    · linarith only [h3671, h3762, hlam]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3736, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3738_1, u2elo1]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    rcases p3738_3 (m.d 0 2) (by simp) with h3766 | h3766
                                    · linarith only [h0, h3766, hlam]
                                    · linarith only [h3673, h3766, hlam]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3671, hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3677, hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3683, hlam, p3738_1]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3734, hlam, p3738_1]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3672, hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3678, hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3738_1, u2elo0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h2314, h3674, h3677, h3683, h3734, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3738_1, u2elo1]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3673, hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3679, hlam, p3738_0]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h0, h3673, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3738_1, u2elo1]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [h3736, hlam, p3738_1]
                                  · have p3738_0 := h3738c.1
                                    have p3738_1 := h3738c.2.1
                                    have p3738_2 := h3738c.2.2.1
                                    have p3738_3 := h3738c.2.2.2
                                    linarith only [hlam, p3738_0]
                                · linarith only [h2314, h3674, h3676, h3677, h3683, h3737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3785 | h3785
                                · linarith only [h2314, h3674, h3677, h3736, h3785, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · linarith only [h2314, h3674, h3676, h3677, h3683, h3785, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h2314, h3426, h3674, h3676, h3677, h3682, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h2314, h3675, h3681, hlam]
                    · linarith only [h2314, h3674, h3680, hlam]
                  · linarith only [h0, h3679, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h3678, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h3677, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3794 | h3794
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3795 | h3795
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3796 | h3796
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3797 | h3797
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3798 | h3798
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3799 | h3799
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3800 | h3800
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3801 | h3801
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3802 | h3802
                              · linarith only [h3672, h3676, h3802, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3804 | h3804
                                · linarith only [h3672, h3676, h3800, h3804, hlam]
                                · rcases h2bigk with h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c | h3806c
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h0, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3801, h3804, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3806_1, u2elo0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    rcases p3806_3 (m.d 0 2) (by simp) with h3810 | h3810
                                    · rcases p3806_3 (m.d 1 2) (by simp) with h3811 | h3811
                                      · rcases p3806_3 (m.d 2 3) (by simp) with h3812 | h3812
                                        · linarith only [h3671, h3812, hlam]
                                        · linarith only [h3800, h3812, hlam]
                                      · linarith only [h3795, h3811, hlam]
                                    · linarith only [h3810, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    rcases p3806_3 (m.d 0 2) (by simp) with h3817 | h3817
                                    · rcases p3806_3 (m.d 1 2) (by simp) with h3818 | h3818
                                      · rcases p3806_3 (m.d 2 3) (by simp) with h3819 | h3819
                                        · linarith only [h3671, h3819, hlam]
                                        · linarith only [h3801, h3819, hlam]
                                      · linarith only [h3796, h3818, hlam]
                                    · linarith only [h3817, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3806_1, u2elo1]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3801, h3804, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3806_1, u2elo1]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    rcases p3806_3 (m.d 0 2) (by simp) with h3827 | h3827
                                    · linarith only [h0, h3827, hlam]
                                    · linarith only [h3672, h3827, hlam]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    rcases p3806_3 (m.d 0 2) (by simp) with h3830 | h3830
                                    · linarith only [h0, h3830, hlam]
                                    · linarith only [h3673, h3830, hlam]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3671, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3794, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3671, h3800, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3806_1, u2elo0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h0, h3671, h3801, h3804, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3806_1, u2elo1]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3672, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3795, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3800, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3802, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3673, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3796, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h3801, hlam, p3806_0]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [h0, h3673, h3800, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3806_1, u2elo1]
                                  · have p3806_0 := h3806c.1
                                    have p3806_1 := h3806c.2.1
                                    have p3806_2 := h3806c.2.2.1
                                    have p3806_3 := h3806c.2.2.2
                                    linarith only [hlam, p3806_0]
                            · linarith only [h3675, h3676, h3794, h3797, h3799, h3800, h3801, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h3674, h3676, h3794, h3797, h3799, h3800, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3850 | h3850
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3851 | h3851
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3852 | h3852
                              · linarith only [h3672, h3799, h3852, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3854 | h3854
                                · linarith only [h3676, h3850, h3854, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                                · rcases h2bigk with h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h0, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h0, h3851, h3854, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3856_1, u2elo1]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    rcases p3856_3 (m.d 0 2) (by simp) with h3860 | h3860
                                    · rcases p3856_3 (m.d 1 2) (by simp) with h3861 | h3861
                                      · rcases p3856_3 (m.d 2 3) (by simp) with h3862 | h3862
                                        · linarith only [h3671, h3862, hlam]
                                        · linarith only [h3850, h3862, hlam]
                                      · linarith only [h3795, h3861, hlam]
                                    · linarith only [h3860, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    rcases p3856_3 (m.d 0 2) (by simp) with h3867 | h3867
                                    · rcases p3856_3 (m.d 1 2) (by simp) with h3868 | h3868
                                      · rcases p3856_3 (m.d 2 3) (by simp) with h3869 | h3869
                                        · linarith only [h3671, h3869, hlam]
                                        · linarith only [h3851, h3869, hlam]
                                      · linarith only [h3796, h3868, hlam]
                                    · linarith only [h3867, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3856_1, u2elo1]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3851, h3854, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3856_1, u2elo1]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    rcases p3856_3 (m.d 0 2) (by simp) with h3877 | h3877
                                    · linarith only [h0, h3877, hlam]
                                    · linarith only [h3672, h3877, hlam]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    rcases p3856_3 (m.d 0 2) (by simp) with h3880 | h3880
                                    · linarith only [h0, h3880, hlam]
                                    · linarith only [h3673, h3880, hlam]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3671, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3794, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3671, h3850, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3856_1, u2elo0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h0, h3671, h3851, h3854, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3856_1, u2elo1]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3672, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3795, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3850, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3852, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3673, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3796, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h3851, hlam, p3856_0]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [h0, h3673, h3850, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3856_1, u2elo1]
                                  · have p3856_0 := h3856c.1
                                    have p3856_1 := h3856c.2.1
                                    have p3856_2 := h3856c.2.2.1
                                    have p3856_3 := h3856c.2.2.2
                                    linarith only [hlam, p3856_0]
                            · linarith only [h0, h3671, h3675, h3850, h3851, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3899 | h3899
                            · linarith only [h0, h3671, h3674, h3850, h3899, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3901 | h3901
                              · linarith only [h0, h3671, h3674, h3676, h3850, h3901, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3903 | h3903
                                · linarith only [h3674, h3676, h3903, hlam]
                                · rcases h2bigk with h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c | h3905c
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h0, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    rcases p3905_3 (m.d 0 2) (by simp) with h3908 | h3908
                                    · rcases p3905_3 (m.d 1 2) (by simp) with h3909 | h3909
                                      · rcases p3905_3 (m.d 2 3) (by simp) with h3910 | h3910
                                        · linarith only [h3910, hlam, p3905_0]
                                        · rcases p3905_3 (m.d 2 4) (by simp) with h3912 | h3912
                                          · linarith only [h3672, h3912, hlam]
                                          · linarith only [h3850, h3912, hlam]
                                      · linarith only [h3794, h3909, hlam]
                                    · linarith only [h3908, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    rcases p3905_3 (m.d 0 2) (by simp) with h3917 | h3917
                                    · rcases p3905_3 (m.d 1 2) (by simp) with h3918 | h3918
                                      · rcases p3905_3 (m.d 2 3) (by simp) with h3919 | h3919
                                        · linarith only [h3671, h3919, hlam]
                                        · rcases p3905_3 (m.d 2 4) (by simp) with h3921 | h3921
                                          · linarith only [h3921, hlam, p3905_0]
                                          · rcases p3905_3 (m.d 2 5) (by simp) with h3923 | h3923
                                            · linarith only [h3673, h3923, hlam]
                                            · linarith only [h3901, h3923, hlam]
                                      · linarith only [h3795, h3918, hlam]
                                    · linarith only [h3917, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    rcases p3905_3 (m.d 0 2) (by simp) with h3928 | h3928
                                    · rcases p3905_3 (m.d 1 2) (by simp) with h3929 | h3929
                                      · rcases p3905_3 (m.d 2 3) (by simp) with h3930 | h3930
                                        · linarith only [h3671, h3930, hlam]
                                        · rcases p3905_3 (m.d 2 4) (by simp) with h3932 | h3932
                                          · linarith only [h3672, h3932, hlam]
                                          · rcases p3905_3 (m.d 2 5) (by simp) with h3934 | h3934
                                            · linarith only [h3934, hlam, p3905_0]
                                            · rcases h3bigk with h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c | h3936c
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h2314, hlam, p3936_1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                rcases p3936_3 (m.d 0 3) (by simp) with h3939 | h3939
                                                · rcases p3936_3 (m.d 1 3) (by simp) with h3940 | h3940
                                                  · rcases p3936_3 (m.d 2 3) (by simp) with h3941 | h3941
                                                    · linarith only [h3671, h3941, hlam]
                                                    · rcases p3936_3 (m.d 3 4) (by simp) with h3943 | h3943
                                                      · linarith only [h3674, h3943, hlam]
                                                      · linarith only [h3850, h3943, hlam]
                                                  · linarith only [h3794, h3940, hlam]
                                                · linarith only [h3671, h3939, hlam]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h0, h3671, h3850, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3936_1, u2elo1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h0, h3671, h3899, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3936_1, u2elo1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3674, h3850, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3936_1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                rcases p3936_3 (m.d 0 3) (by simp) with h3952 | h3952
                                                · linarith only [h2314, h3952, hlam]
                                                · linarith only [h3671, h3952, hlam]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3794, h3850, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3936_1, u2elo1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3794, h3850, h3903, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3936_1, u2elo1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3671, hlam, p3936_1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3794, hlam, p3936_1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3850, hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3899, hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3674, hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3797, hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3674, h3676, hc23, hc45, hlam, hphi, ht34, p3936_1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3903, hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3675, hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h3798, hlam, p3936_0]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h2314, h3675, h3794, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3936_1, u2elo1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [h2314, h3675, h3794, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3936_1, u2elo1]
                                              · have p3936_0 := h3936c.1
                                                have p3936_1 := h3936c.2.1
                                                have p3936_2 := h3936c.2.2.1
                                                have p3936_3 := h3936c.2.2.2
                                                linarith only [hlam, p3936_0]
                                      · linarith only [h3796, h3929, hlam]
                                    · linarith only [h3928, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3905_1, u2elo1]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    rcases p3905_3 (m.d 0 2) (by simp) with h3976 | h3976
                                    · linarith only [h0, h3976, hlam]
                                    · linarith only [h3671, h3976, hlam]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    rcases p3905_3 (m.d 0 2) (by simp) with h3979 | h3979
                                    · linarith only [h0, h3979, hlam]
                                    · linarith only [h3672, h3979, hlam]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    rcases p3905_3 (m.d 0 2) (by simp) with h3982 | h3982
                                    · linarith only [h0, h3982, hlam]
                                    · linarith only [h3673, h3982, hlam]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h3671, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h3794, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h3850, hlam, p3905_1]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h3899, hlam, p3905_1]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h3672, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h3795, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h3672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3905_1, u2elo0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h3901, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h3673, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h3796, hlam, p3905_0]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h2314, h3675, h3794, h3899, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3905_1, u2elo1]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [h2314, h3675, h3794, h3899, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3905_1, u2elo1]
                                  · have p3905_0 := h3905c.1
                                    have p3905_1 := h3905c.2.1
                                    have p3905_2 := h3905c.2.2.1
                                    have p3905_3 := h3905c.2.2.2
                                    linarith only [hlam, p3905_0]
                      · linarith only [h2314, h3675, h3798, hlam]
                    · linarith only [h2314, h3674, h3797, hlam]
                  · linarith only [h0, h3796, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h3795, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h3794, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4005 | h4005
            · linarith only [h3674, h3675, h4005, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4007 | h4007
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4008 | h4008
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4009 | h4009
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4010 | h4010
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4011 | h4011
                      · linarith only [h3674, h3675, h4007, h4011, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4013 | h4013
                        · linarith only [h4010, h4011, h4013, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4015 | h4015
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4016 | h4016
                            · linarith only [h2314, h4011, h4016, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4018 | h4018
                              · linarith only [h2314, h4011, h4013, h4018, hc01, hlam, hphi, ht12, u2elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4020 | h4020
                                · linarith only [h0, h3673, h4005, h4015, h4016, h4020, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases h2bigk with h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c | h4022c
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h0, hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h0, h4015, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4022_1, u2elo1]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    rcases p4022_3 (m.d 0 2) (by simp) with h4026 | h4026
                                    · rcases p4022_3 (m.d 1 2) (by simp) with h4027 | h4027
                                      · rcases p4022_3 (m.d 2 3) (by simp) with h4028 | h4028
                                        · linarith only [h3671, h4028, hlam]
                                        · linarith only [h4015, h4028, hlam]
                                      · linarith only [h4008, h4027, hlam]
                                    · linarith only [h4026, hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h0, h4015, h4016, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4022_1, u2elo1]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [hc02, hlam, hphi, p4022_1, u2elo1]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h4015, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4022_1, u2elo1]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    rcases p4022_3 (m.d 0 2) (by simp) with h4037 | h4037
                                    · linarith only [h0, h4037, hlam]
                                    · linarith only [h3672, h4037, hlam]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h4015, h4016, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4022_1, u2elo1]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h3671, hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h4007, hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h3673, h4015, h4016, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4022_1, u2elo0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h4016, hlam, p4022_1]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h3672, hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h4008, hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h4015, hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h4018, hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h3673, hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h4009, hlam, p4022_0]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h0, h3673, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4022_1, u2elo1]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [h0, h3673, h4015, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4022_1, u2elo1]
                                  · have p4022_0 := h4022c.1
                                    have p4022_1 := h4022c.2.1
                                    have p4022_2 := h4022c.2.2.1
                                    have p4022_3 := h4022c.2.2.2
                                    linarith only [hlam, p4022_0]
                          · linarith only [h2314, h3674, h4011, h4015, hc23, hc35, hlam, hphi]
                    · linarith only [h2314, h3674, h4010, hlam]
                  · linarith only [h0, h3673, h4009, hlam]
                · linarith only [h0, h4008, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h4007, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4061 | h4061
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4062 | h4062
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4063 | h4063
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4064 | h4064
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4065 | h4065
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4066 | h4066
                    · linarith only [h3674, h4061, h4063, h4066, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4068 | h4068
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4069 | h4069
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4070 | h4070
                          · linarith only [h3671, h4066, h4070, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4072 | h4072
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4073 | h4073
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4074 | h4074
                                · rcases h2bigk with h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h0, hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h0, h4072, h4074, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4075_1, u2elo1]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h0, h4070, h4072, h4074, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4075_1, u2elo1]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    rcases p4075_3 (m.d 0 2) (by simp) with h4080 | h4080
                                    · rcases p4075_3 (m.d 1 2) (by simp) with h4081 | h4081
                                      · rcases p4075_3 (m.d 2 3) (by simp) with h4082 | h4082
                                        · linarith only [h3671, h4082, hlam]
                                        · linarith only [h4072, h4082, hlam]
                                      · linarith only [h4065, h4081, hlam]
                                    · linarith only [h4080, hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [hc02, hlam, hphi, p4075_1, u2elo1]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h4072, h4074, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4075_1, u2elo1]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h4070, h4072, h4074, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4075_1, u2elo1]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    rcases p4075_3 (m.d 0 2) (by simp) with h4091 | h4091
                                    · linarith only [h0, h4091, hlam]
                                    · linarith only [h3673, h4091, hlam]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h3671, hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h4063, hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h4070, hlam, p4075_1]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h3672, h4070, h4072, h4074, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4075_1, u2elo0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h3672, hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h4064, hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h0, h3672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4075_1, u2elo1]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h0, h3672, h4072, h4074, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4075_1, u2elo1]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h3673, hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h4065, hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h4072, hlam, p4075_0]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [h4073, hlam, p4075_1]
                                  · have p4075_0 := h4075c.1
                                    have p4075_1 := h4075c.2.1
                                    have p4075_2 := h4075c.2.2.1
                                    have p4075_3 := h4075c.2.2.2
                                    linarith only [hlam, p4075_0]
                                · linarith only [h3426, h4066, h4068, h4074, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h0, h3672, h4062, h4070, h4072, h4073, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h2314, h4061, h4066, h4072, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h2314, h3672, h4061, h4062, h4066, h4069, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h2314, h4061, h4068, hlam]
                  · linarith only [h0, h3673, h4065, hlam]
                · linarith only [h0, h4064, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h4063, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h3674, h4061, h4062, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4118 | h4118
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4119 | h4119
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4120 | h4120
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4121 | h4121
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4122 | h4122
                    · linarith only [h2314, h3674, h4119, h4122, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4124 | h4124
                      · linarith only [h2314, h4061, h4122, h4124, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4126 | h4126
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4127 | h4127
                          · linarith only [h3671, h3674, h4127, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4129 | h4129
                            · linarith only [h2314, h4124, h4129, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4131 | h4131
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4132 | h4132
                                · rcases h2bigk with h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h0, hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    rcases p4133_3 (m.d 0 2) (by simp) with h4136 | h4136
                                    · rcases p4133_3 (m.d 1 2) (by simp) with h4137 | h4137
                                      · rcases p4133_3 (m.d 2 3) (by simp) with h4138 | h4138
                                        · linarith only [h4138, hlam, p4133_0]
                                        · rcases p4133_3 (m.d 2 4) (by simp) with h4140 | h4140
                                          · linarith only [h3672, h4140, hlam]
                                          · linarith only [h4127, h4140, hlam]
                                      · linarith only [h4119, h4137, hlam]
                                    · linarith only [h4136, hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h0, h4131, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4133_1, u2elo1]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    rcases p4133_3 (m.d 0 2) (by simp) with h4146 | h4146
                                    · rcases p4133_3 (m.d 1 2) (by simp) with h4147 | h4147
                                      · rcases p4133_3 (m.d 2 3) (by simp) with h4148 | h4148
                                        · linarith only [h3671, h4148, hlam]
                                        · rcases p4133_3 (m.d 2 4) (by simp) with h4150 | h4150
                                          · linarith only [h3672, h4150, hlam]
                                          · linarith only [h4131, h4150, hlam]
                                      · linarith only [h4121, h4147, hlam]
                                    · linarith only [h4146, hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [hc02, hlam, hphi, p4133_1, u2elo1]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    rcases p4133_3 (m.d 0 2) (by simp) with h4157 | h4157
                                    · linarith only [h0, h4157, hlam]
                                    · linarith only [h3671, h4157, hlam]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h4131, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4133_1, u2elo1]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    rcases p4133_3 (m.d 0 2) (by simp) with h4161 | h4161
                                    · linarith only [h0, h4161, hlam]
                                    · linarith only [h3673, h4161, hlam]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h3671, hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h4119, hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h4127, hlam, p4133_1]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h4129, hlam, p4133_1]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h3672, hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h4120, hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h3672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4133_1, u2elo0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h0, h3672, h4129, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4133_1, u2elo1]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h3673, hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h4121, hlam, p4133_0]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h0, h3673, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4133_1, u2elo1]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [h4131, hlam, p4133_1]
                                  · have p4133_0 := h4133c.1
                                    have p4133_1 := h4133c.2.1
                                    have p4133_2 := h4133c.2.2.1
                                    have p4133_3 := h4133c.2.2.2
                                    linarith only [hlam, p4133_0]
                                · linarith only [h0, h2314, h3672, h3674, h4118, h4132, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4180 | h4180
                                · rcases h2bigk with h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h0, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    rcases p4181_3 (m.d 0 2) (by simp) with h4184 | h4184
                                    · rcases p4181_3 (m.d 1 2) (by simp) with h4185 | h4185
                                      · rcases p4181_3 (m.d 2 3) (by simp) with h4186 | h4186
                                        · linarith only [h4186, hlam, p4181_0]
                                        · rcases p4181_3 (m.d 2 4) (by simp) with h4188 | h4188
                                          · linarith only [h3672, h4188, hlam]
                                          · linarith only [h4127, h4188, hlam]
                                      · linarith only [h4119, h4185, hlam]
                                    · linarith only [h4184, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    rcases p4181_3 (m.d 0 2) (by simp) with h4193 | h4193
                                    · rcases p4181_3 (m.d 1 2) (by simp) with h4194 | h4194
                                      · rcases p4181_3 (m.d 2 3) (by simp) with h4195 | h4195
                                        · linarith only [h3671, h4195, hlam]
                                        · rcases p4181_3 (m.d 2 4) (by simp) with h4197 | h4197
                                          · linarith only [h4197, hlam, p4181_0]
                                          · rcases p4181_3 (m.d 2 5) (by simp) with h4199 | h4199
                                            · linarith only [h3673, h4199, hlam]
                                            · linarith only [h4131, h4199, hlam]
                                      · linarith only [h4120, h4194, hlam]
                                    · linarith only [h4193, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    rcases p4181_3 (m.d 0 2) (by simp) with h4204 | h4204
                                    · rcases p4181_3 (m.d 1 2) (by simp) with h4205 | h4205
                                      · rcases p4181_3 (m.d 2 3) (by simp) with h4206 | h4206
                                        · linarith only [h3671, h4206, hlam]
                                        · rcases p4181_3 (m.d 2 4) (by simp) with h4208 | h4208
                                          · linarith only [h3672, h4208, hlam]
                                          · rcases p4181_3 (m.d 2 5) (by simp) with h4210 | h4210
                                            · linarith only [h4210, hlam, p4181_0]
                                            · rcases h3bigk with h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c | h4212c
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [hlam, p4212_0]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h2314, hlam, p4212_1]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h2314, h4124, h4180, hc23, hc34, hlam, hphi, p4212_1]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h3674, hlam, p4212_0]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h4061, hlam, p4212_0]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h4124, h4180, hc03, hc34, hlam, hphi, p4212_1]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [hlam, p4212_0]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h4124, h4180, hc23, hc34, hlam, hphi, p4212_1]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h4122, hlam, p4212_0]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h4124, hlam, p4212_0]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h3671, hlam, p4212_1]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h4119, hlam, p4212_1]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [hlam, p4212_0]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h4127, hlam, p4212_0]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h4129, hlam, p4212_0]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                rcases p4212_3 (m.d 0 3) (by simp) with h4228 | h4228
                                                · linarith only [h4228, hlam, p4212_0]
                                                · rcases p4212_3 (m.d 1 3) (by simp) with h4230 | h4230
                                                  · linarith only [h4122, h4230, hlam]
                                                  · linarith only [h2314, h4230, hlam]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h2314, hc01, hc34, hlam, hphi, ht12, ht23, p4212_1]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                rcases p4212_3 (m.d 0 3) (by simp) with h4234 | h4234
                                                · linarith only [h3674, h4234, hlam]
                                                · linarith only [h3671, h4234, hlam]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [hlam, p4212_0]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h0, h2314, h3672, h4061, h4118, h4127, h4131, hc01, hc23, hc34, hlam, hphi, ht12, p4212_1, u2elo1]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                rcases p4212_3 (m.d 0 3) (by simp) with h4239 | h4239
                                                · linarith only [h4239, hlam, p4212_0]
                                                · rcases p4212_3 (m.d 1 3) (by simp) with h4241 | h4241
                                                  · linarith only [h4124, h4241, hlam]
                                                  · linarith only [h2314, h4241, hlam]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h0, h2314, h3672, h4118, h4127, h4131, hc01, hc23, hc35, hlam, hphi, ht12, p4212_1, u2elo1]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                rcases p4212_3 (m.d 0 3) (by simp) with h4245 | h4245
                                                · linarith only [h4061, h4245, hlam]
                                                · linarith only [h3671, h4245, hlam]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [h4180, hlam, p4212_1]
                                              · have p4212_0 := h4212c.1
                                                have p4212_1 := h4212c.2.1
                                                have p4212_2 := h4212c.2.2.1
                                                have p4212_3 := h4212c.2.2.2
                                                linarith only [hlam, p4212_0]
                                      · linarith only [h4121, h4205, hlam]
                                    · linarith only [h4204, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h3672, h4118, h4127, h4131, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4181_1, u2elo1]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    rcases p4181_3 (m.d 0 2) (by simp) with h4254 | h4254
                                    · linarith only [h0, h4254, hlam]
                                    · linarith only [h3671, h4254, hlam]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    rcases p4181_3 (m.d 0 2) (by simp) with h4257 | h4257
                                    · linarith only [h0, h4257, hlam]
                                    · linarith only [h3672, h4257, hlam]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    rcases p4181_3 (m.d 0 2) (by simp) with h4260 | h4260
                                    · linarith only [h0, h4260, hlam]
                                    · linarith only [h3673, h4260, hlam]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h3671, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h4119, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h4127, hlam, p4181_1]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h4129, hlam, p4181_1]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h3672, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h4120, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h3672, h4118, h4131, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4181_1]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h4131, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h3673, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h4121, hlam, p4181_0]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h0, h3673, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4181_1, u2elo1]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [h0, h3672, h4118, h4131, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4181_1, u2elo1]
                                  · have p4181_0 := h4181c.1
                                    have p4181_1 := h4181c.2.1
                                    have p4181_2 := h4181c.2.2.1
                                    have p4181_3 := h4181c.2.2.2
                                    linarith only [hlam, p4181_0]
                                · linarith only [h0, h2314, h3672, h3674, h4118, h4180, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h2314, h3672, h4118, h4122, h4126, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h4121, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h4120, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h4119, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4283 | h4283
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4284 | h4284
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4285 | h4285
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4286 | h4286
                    · linarith only [h2314, h3674, h4283, h4286, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4288 | h4288
                      · linarith only [h2314, h4061, h4284, h4286, h4288, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4290 | h4290
                        · linarith only [h2314, h3674, h4118, h4284, h4290, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4292 | h4292
                          · linarith only [h3671, h3674, h4292, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4294 | h4294
                            · linarith only [h3672, h4288, h4292, h4294, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4296 | h4296
                              · linarith only [h0, h3672, h4118, h4296, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4298 | h4298
                                · linarith only [h2314, h4286, h4290, h4298, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h2314, h4286, h4298, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h3673, h4285, hlam]
                · linarith only [h0, h4284, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h4283, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4304 | h4304
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4305 | h4305
          · linarith only [h3671, h3673, h4305, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4307 | h4307
            · linarith only [h3672, h3673, h4307, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4309 | h4309
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4310 | h4310
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4311 | h4311
                  · linarith only [h3673, h4311, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h4311, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h2314, h4309, h4310, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h3671, h3673, h4309, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4316 | h4316
          · linarith only [h3672, h3673, h4304, h4316, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4318 | h4318
            · linarith only [h3672, h3673, h4318, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4320 | h4320
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4321 | h4321
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4322 | h4322
                  · linarith only [h3673, h4322, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h4322, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h2314, h4320, h4321, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h3671, h4320, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4327 | h4327
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4328 | h4328
        · linarith only [h3671, h3672, h4328, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4330 | h4330
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4331 | h4331
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4332 | h4332
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4333 | h4333
                · linarith only [h3672, h4333, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h4333, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h4332, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h3671, h3672, h4330, h4331, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4338 | h4338
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4339 | h4339
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4340 | h4340
                · linarith only [h3672, h4340, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h4340, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h4339, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h3672, h4327, h4338, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4345 | h4345
        · linarith only [h3671, h3672, h4345, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4347 | h4347
          · linarith only [h3671, h4327, h4347, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4349 | h4349
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4350 | h4350
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4351 | h4351
                · linarith only [h3672, h4351, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h4351, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h4350, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4355 | h4355
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4356 | h4356
                · linarith only [h3672, h4356, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h4356, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h4355, hc01, hlam, hphi, ht12, u2elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h4360 | h4360
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4361 | h4361
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4362 | h4362
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4363 | h4363
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4364 | h4364
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4365 | h4365
              · linarith only [h3671, h4365, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h4365, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4368 | h4368
              · linarith only [h3671, h4360, h4368, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h0, h4368, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h3671, h4361, h4363, hlam]
        · linarith only [h3671, h4360, h4362, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4373 | h4373
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4374 | h4374
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4375 | h4375
            · linarith only [h4360, h4361, h4375, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4377 | h4377
              · linarith only [h3671, h4360, h4377, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h0, h4377, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4380 | h4380
            · linarith only [h3671, h4360, h4374, h4380, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4382 | h4382
              · linarith only [h3671, h4360, h4382, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h0, h4382, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h3671, h4360, h4373, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4386 | h4386
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4387 | h4387
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4388 | h4388
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4389 | h4389
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4390 | h4390
              · linarith only [h3671, h4390, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h4390, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h4360, h4386, h4389, hlam]
          · linarith only [h4360, h4386, h4387, h4388, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4395 | h4395
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4396 | h4396
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4397 | h4397
              · linarith only [h3671, h4386, h4397, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h4397, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h3671, h4386, h4387, h4396, hlam]
          · linarith only [h3671, h4386, h4395, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4402 | h4402
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4403 | h4403
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4404 | h4404
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4405 | h4405
              · linarith only [h0, h3671, h4405, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h4405, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4408 | h4408
              · linarith only [h0, h3671, h4408, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h4408, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4411 | h4411
            · linarith only [h4402, h4403, h4411, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4413 | h4413
              · linarith only [h0, h3671, h4413, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h4413, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4416 | h4416
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4417 | h4417
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4418 | h4418
              · linarith only [h0, h3671, h4418, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h4418, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h4402, h4416, h4417, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4422 | h4422
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4423 | h4423
              · linarith only [h0, h3671, h4423, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h4423, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4426 | h4426
              · linarith only [h0, h3671, h4426, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h4426, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3426 | h3426
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x1_x1_x0 m hb2 hb3 hb5 h0 h2314 h3426
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x1_x1_x1 m hb2 hb3 hb5 h0 h2314 h3426

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h2314 | h2314
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x1_x0 m hb2 hb3 hb5 h0 h2314
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x1_x1 m hb2 hb3 hb5 h0 h2314

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0 m hb2 hb3 hb5 h0
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x1 m hb2 hb3 hb5 h0

end R2N4
