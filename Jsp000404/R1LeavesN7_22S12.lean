import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S7
import Jsp000404.R1LeavesN7_22S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6476000 in
set_option maxHeartbeats 6476000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s4 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h3609 | h3609
  · rcases m.htr 0 1 4 (by decide) (by decide) with h3610 | h3610
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3611 | h3611
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3612 | h3612
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3613 | h3613
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3614 | h3614
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3615 | h3615
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3616 | h3616
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3617 | h3617
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3618 | h3618
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3619 | h3619
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3620 | h3620
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3621 | h3621
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3622 | h3622
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3623 | h3623
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3624 | h3624
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3625 | h3625
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3626 | h3626
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3627 | h3627
                                      · linarith only [h0, h3609, h3618, h3624, h3627, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                      · linarith only [h3627, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h3609, h3621, h3623, h3626, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h3625, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h0, h3609, h3621, h3624, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h3623, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h3622, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3635 | h3635
                            · linarith only [h0, h3609, h3615, h3621, h3635, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h3635, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h3620, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h3611, h3613, h3619, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h3612, h3618, hlam]
                  · linarith only [h3617, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h3615, h3616, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3643 | h3643
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3644 | h3644
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3645 | h3645
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3646 | h3646
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3647 | h3647
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3648 | h3648
                          · linarith only [h3609, h3615, h3643, h3648, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3650 | h3650
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3651 | h3651
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3652 | h3652
                                · linarith only [h0, h3609, h3610, h3615, h3645, h3651, h3652, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3654 | h3654
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3655 | h3655
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3656 | h3656
                                      · rcases h0bigk with h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [hlam, p3657_0]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h0, hlam, p3657_1]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h0, h3643, h3656, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3657_1]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h0, h3615, h3643, h3656, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3657_1]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          rcases p3657_3 (m.d 0 1) (by simp) with h3662 | h3662
                                          · rcases p3657_3 (m.d 0 2) (by simp) with h3663 | h3663
                                            · rcases p3657_3 (m.d 0 3) (by simp) with h3664 | h3664
                                              · linarith only [h3609, h3664, hlam]
                                              · linarith only [h3643, h3664, hlam]
                                            · linarith only [h3614, h3663, hlam]
                                          · linarith only [h3611, h3662, hlam]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h0, h3609, h3645, h3654, h3656, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3657_1]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [hlam, p3657_0]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          rcases p3657_3 (m.d 0 1) (by simp) with h3671 | h3671
                                          · linarith only [h0, h3671, hlam]
                                          · linarith only [h3609, h3671, hlam]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          rcases p3657_3 (m.d 0 1) (by simp) with h3674 | h3674
                                          · linarith only [h0, h3674, hlam]
                                          · linarith only [h3610, h3674, hlam]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          rcases p3657_3 (m.d 0 1) (by simp) with h3677 | h3677
                                          · linarith only [h0, h3677, hlam]
                                          · linarith only [h3611, h3677, hlam]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h3609, hlam, p3657_1]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h3612, hlam, p3657_1]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [hlam, p3657_0]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h3615, hlam, p3657_1]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          rcases p3657_3 (m.d 0 1) (by simp) with h3684 | h3684
                                          · rcases p3657_3 (m.d 0 2) (by simp) with h3685 | h3685
                                            · rcases p3657_3 (m.d 0 3) (by simp) with h3686 | h3686
                                              · rcases p3657_3 (m.d 0 4) (by simp) with h3687 | h3687
                                                · rcases p3657_3 (m.d 0 5) (by simp) with h3688 | h3688
                                                  · linarith only [h3643, h3688, hlam]
                                                  · rcases h0emin with h3690 | h3690 | h3690 | h3690 | h3690
                                                    · linarith only [h0, h3690, hc12, hlam, ht01]
                                                    · rcases h2bigk with h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c | h3692c
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h0, hlam, p3692_1]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        rcases p3692_3 (m.d 0 2) (by simp) with h3695 | h3695
                                                        · rcases p3692_3 (m.d 1 2) (by simp) with h3696 | h3696
                                                          · rcases p3692_3 (m.d 2 3) (by simp) with h3697 | h3697
                                                            · linarith only [h3697, hlam, p3692_0]
                                                            · rcases p3692_3 (m.d 2 4) (by simp) with h3699 | h3699
                                                              · linarith only [h3613, h3699, hlam]
                                                              · linarith only [h3652, h3699, hlam]
                                                          · linarith only [h3645, h3696, hlam]
                                                        · linarith only [h3695, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        rcases p3692_3 (m.d 0 2) (by simp) with h3704 | h3704
                                                        · rcases p3692_3 (m.d 1 2) (by simp) with h3705 | h3705
                                                          · rcases p3692_3 (m.d 2 3) (by simp) with h3706 | h3706
                                                            · linarith only [h3612, h3706, hlam]
                                                            · rcases p3692_3 (m.d 2 4) (by simp) with h3708 | h3708
                                                              · linarith only [h3708, hlam, p3692_0]
                                                              · rcases p3692_3 (m.d 2 5) (by simp) with h3710 | h3710
                                                                · linarith only [h3614, h3710, hlam]
                                                                · rcases h3bigk with h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c | h3712c
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3615, h3645, h3654, h3656, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3712_1]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3615, h3654, h3656, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3712_1]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3615, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    rcases p3712_3 (m.d 0 3) (by simp) with h3717 | h3717
                                                                    · rcases p3712_3 (m.d 1 3) (by simp) with h3718 | h3718
                                                                      · linarith only [h3609, h3718, hlam]
                                                                      · linarith only [h3650, h3718, hlam]
                                                                    · linarith only [h3717, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3609, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h0, h3609, h3654, h3656, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3712_1]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3648, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h0, h3610, h3648, h3656, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3712_1]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3612, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3645, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3652, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3652, h3656, hc02, hc45, hlam, hphi, ht0b, ht5b, p3692_1, p3712_1]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3611, h3647, h3654, h3656, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3657_1, p3712_1]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    rcases p3712_3 (m.d 0 3) (by simp) with h3733 | h3733
                                                                    · linarith only [h3615, h3733, hlam]
                                                                    · linarith only [h3609, h3733, hlam]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    rcases p3712_3 (m.d 0 3) (by simp) with h3736 | h3736
                                                                    · linarith only [h3615, h3736, hlam]
                                                                    · linarith only [h3612, h3736, hlam]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3611, h3615, h3647, h3654, hlam, p3657_1, p3712_2]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3643, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3650, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3654, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [h3656, hlam, p3712_0]
                                                                  · have p3712_0 := h3712c.1
                                                                    have p3712_1 := h3712c.2.1
                                                                    have p3712_2 := h3712c.2.2.1
                                                                    have p3712_3 := h3712c.2.2.2
                                                                    linarith only [hlam, p3712_0]
                                                          · linarith only [h3646, h3705, hlam]
                                                        · linarith only [h3704, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        rcases p3692_3 (m.d 0 2) (by simp) with h3748 | h3748
                                                        · rcases p3692_3 (m.d 1 2) (by simp) with h3749 | h3749
                                                          · rcases p3692_3 (m.d 2 3) (by simp) with h3750 | h3750
                                                            · linarith only [h3612, h3750, hlam]
                                                            · linarith only [h3654, h3750, hlam]
                                                          · linarith only [h3647, h3749, hlam]
                                                        · linarith only [h3748, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h3690, hc12, hlam, ht01, p3692_1]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        rcases p3692_3 (m.d 0 2) (by simp) with h3757 | h3757
                                                        · linarith only [h0, h3757, hlam]
                                                        · linarith only [h3612, h3757, hlam]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        rcases p3692_3 (m.d 0 2) (by simp) with h3760 | h3760
                                                        · linarith only [h0, h3760, hlam]
                                                        · linarith only [h3613, h3760, hlam]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h0, h3609, h3611, h3647, hlam, p3657_1, p3692_2]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h3612, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h3645, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h3652, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h0, h3610, h3646, h3652, h3654, h3656, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3692_1]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h3613, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h3646, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h0, h3610, h3646, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3692_1]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h0, h3610, h3646, h3654, h3656, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3692_1]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h3614, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h3647, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h3654, hlam, p3692_1]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [h3655, hlam, p3692_0]
                                                      · have p3692_0 := h3692c.1
                                                        have p3692_1 := h3692c.2.1
                                                        have p3692_2 := h3692c.2.2.1
                                                        have p3692_3 := h3692c.2.2.2
                                                        linarith only [hlam, p3692_0]
                                                    · linarith only [h3615, h3690, hc34, hlam, ht01, ht12, ht23]
                                                    · linarith only [h0, h3610, h3690, hc12, hlam, ht01]
                                                    · linarith only [h3690, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                                · linarith only [h3644, h3687, hlam]
                                              · linarith only [h3643, h3686, hlam]
                                            · linarith only [h3614, h3685, hlam]
                                          · linarith only [h3611, h3684, hlam]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h3610, hlam, p3657_0]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h3613, hlam, p3657_0]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h0, h3610, h3612, h3654, h3656, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3657_1]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [hlam, p3657_0]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          rcases p3657_3 (m.d 0 1) (by simp) with h3790 | h3790
                                          · rcases p3657_3 (m.d 0 2) (by simp) with h3791 | h3791
                                            · rcases p3657_3 (m.d 0 3) (by simp) with h3792 | h3792
                                              · linarith only [h3615, h3792, hlam]
                                              · linarith only [h3643, h3792, hlam]
                                            · linarith only [h3614, h3791, hlam]
                                          · linarith only [h3611, h3790, hlam]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h3611, hlam, p3657_0]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h3614, hlam, p3657_1]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h3643, hlam, p3657_0]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [h3644, hlam, p3657_1]
                                        · have p3657_0 := h3657c.1
                                          have p3657_1 := h3657c.2.1
                                          have p3657_2 := h3657c.2.2.1
                                          have p3657_3 := h3657c.2.2.2
                                          linarith only [hlam, p3657_0]
                                      · linarith only [h3656, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h3651, h3655, hc24, hlam, hphi, ht45, u5elo1]
                                  · linarith only [h3654, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h3648, h3651, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h3645, h3650, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h3647, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h3610, h3613, h3646, hlam]
                    · linarith only [h0, h3611, h3612, h3645, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3615, h3643, h3644, hc35, hlam, hphi, u5elo4]
                · linarith only [h3643, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h3614, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h3610, h3613, hlam]
        · linarith only [h0, h3609, h3612, hlam]
      · linarith only [h3609, h3611, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3816 | h3816
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3817 | h3817
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3818 | h3818
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3819 | h3819
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3820 | h3820
              · linarith only [h3609, h3610, h3820, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3822 | h3822
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3823 | h3823
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3824 | h3824
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3825 | h3825
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3826 | h3826
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3827 | h3827
                          · linarith only [h3609, h3610, h3820, h3827, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3829 | h3829
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3830 | h3830
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3831 | h3831
                                · linarith only [h3609, h3610, h3827, h3829, h3831, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3833 | h3833
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3834 | h3834
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3835 | h3835
                                      · rcases h0bigk with h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [hlam, p3836_0]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h0, hlam, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3609, h3610, h3824, h3825, h3833, h3835, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3610, hlam, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          rcases p3836_3 (m.d 0 1) (by simp) with h3841 | h3841
                                          · rcases p3836_3 (m.d 0 2) (by simp) with h3842 | h3842
                                            · rcases p3836_3 (m.d 0 3) (by simp) with h3843 | h3843
                                              · linarith only [h3609, h3843, hlam]
                                              · linarith only [h3822, h3843, hlam]
                                            · linarith only [h3819, h3842, hlam]
                                          · linarith only [h3816, h3841, hlam]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h0, h3609, h3824, h3833, h3835, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [hlam, p3836_0]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          rcases p3836_3 (m.d 0 1) (by simp) with h3850 | h3850
                                          · linarith only [h0, h3850, hlam]
                                          · linarith only [h3609, h3850, hlam]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h0, h3609, h3610, h3824, h3833, h3835, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          rcases p3836_3 (m.d 0 1) (by simp) with h3854 | h3854
                                          · linarith only [h0, h3854, hlam]
                                          · linarith only [h3816, h3854, hlam]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3609, hlam, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3817, hlam, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [hlam, p3836_0]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3820, hlam, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          rcases p3836_3 (m.d 0 1) (by simp) with h3861 | h3861
                                          · rcases p3836_3 (m.d 0 2) (by simp) with h3862 | h3862
                                            · rcases p3836_3 (m.d 0 3) (by simp) with h3863 | h3863
                                              · rcases p3836_3 (m.d 0 4) (by simp) with h3864 | h3864
                                                · rcases p3836_3 (m.d 0 5) (by simp) with h3865 | h3865
                                                  · linarith only [h3822, h3865, hlam]
                                                  · rcases h0emin with h3867 | h3867 | h3867 | h3867 | h3867
                                                    · linarith only [h0, h3867, hc12, hlam, ht01]
                                                    · rcases h2bigk with h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c | h3869c
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h0, hlam, p3869_1]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        rcases p3869_3 (m.d 0 2) (by simp) with h3872 | h3872
                                                        · rcases p3869_3 (m.d 1 2) (by simp) with h3873 | h3873
                                                          · rcases p3869_3 (m.d 2 3) (by simp) with h3874 | h3874
                                                            · linarith only [h3874, hlam, p3869_0]
                                                            · rcases p3869_3 (m.d 2 4) (by simp) with h3876 | h3876
                                                              · linarith only [h3818, h3876, hlam]
                                                              · linarith only [h3831, h3876, hlam]
                                                          · linarith only [h3824, h3873, hlam]
                                                        · linarith only [h3872, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        rcases p3869_3 (m.d 0 2) (by simp) with h3881 | h3881
                                                        · rcases p3869_3 (m.d 1 2) (by simp) with h3882 | h3882
                                                          · rcases p3869_3 (m.d 2 3) (by simp) with h3883 | h3883
                                                            · linarith only [h3817, h3883, hlam]
                                                            · rcases p3869_3 (m.d 2 4) (by simp) with h3885 | h3885
                                                              · linarith only [h3885, hlam, p3869_0]
                                                              · rcases p3869_3 (m.d 2 5) (by simp) with h3887 | h3887
                                                                · linarith only [h3819, h3887, hlam]
                                                                · rcases h3bigk with h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c | h3889c
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h0, h3609, h3824, h3833, h3835, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3889_1]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3609, h3610, h3827, h3833, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3889_1]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3820, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    rcases p3889_3 (m.d 0 3) (by simp) with h3894 | h3894
                                                                    · rcases p3889_3 (m.d 1 3) (by simp) with h3895 | h3895
                                                                      · linarith only [h3609, h3895, hlam]
                                                                      · linarith only [h3829, h3895, hlam]
                                                                    · linarith only [h3894, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3609, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3609, h3610, h3827, h3833, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3889_1]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3827, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3609, h3610, h3827, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3889_1]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3817, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3824, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3831, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3609, h3610, h3824, h3827, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3889_1]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3816, h3826, h3833, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3836_1, p3889_1]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    rcases p3889_3 (m.d 0 3) (by simp) with h3910 | h3910
                                                                    · linarith only [h3820, h3910, hlam]
                                                                    · linarith only [h3609, h3910, hlam]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    rcases p3889_3 (m.d 0 3) (by simp) with h3913 | h3913
                                                                    · linarith only [h3820, h3913, hlam]
                                                                    · linarith only [h3817, h3913, hlam]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3609, h3610, h3816, h3826, h3827, h3833, hlam, p3836_1, p3889_2]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3822, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3829, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3833, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [h3835, hlam, p3889_0]
                                                                  · have p3889_0 := h3889c.1
                                                                    have p3889_1 := h3889c.2.1
                                                                    have p3889_2 := h3889c.2.2.1
                                                                    have p3889_3 := h3889c.2.2.2
                                                                    linarith only [hlam, p3889_0]
                                                          · linarith only [h3825, h3882, hlam]
                                                        · linarith only [h3881, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        rcases p3869_3 (m.d 0 2) (by simp) with h3925 | h3925
                                                        · rcases p3869_3 (m.d 1 2) (by simp) with h3926 | h3926
                                                          · rcases p3869_3 (m.d 2 3) (by simp) with h3927 | h3927
                                                            · linarith only [h3817, h3927, hlam]
                                                            · linarith only [h3833, h3927, hlam]
                                                          · linarith only [h3826, h3926, hlam]
                                                        · linarith only [h3925, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3867, hc12, hlam, ht01, p3869_1]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        rcases p3869_3 (m.d 0 2) (by simp) with h3934 | h3934
                                                        · linarith only [h0, h3934, hlam]
                                                        · linarith only [h3817, h3934, hlam]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        rcases p3869_3 (m.d 0 2) (by simp) with h3937 | h3937
                                                        · linarith only [h0, h3937, hlam]
                                                        · linarith only [h3818, h3937, hlam]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h0, h3609, h3816, h3826, hlam, p3836_1, p3869_2]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3817, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3824, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3831, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3609, h3610, h3824, h3827, h3833, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3869_1]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3818, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3825, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h0, h3818, h3833, h3835, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3869_1]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        rcases p3869_3 (m.d 0 2) (by simp) with h3950 | h3950
                                                        · rcases p3869_3 (m.d 1 2) (by simp) with h3951 | h3951
                                                          · rcases p3869_3 (m.d 2 3) (by simp) with h3952 | h3952
                                                            · linarith only [h3831, h3952, hlam]
                                                            · linarith only [h3833, h3952, hlam]
                                                          · linarith only [h3826, h3951, hlam]
                                                        · linarith only [h3819, h3950, hlam]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3819, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3826, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3833, hlam, p3869_1]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [h3834, hlam, p3869_0]
                                                      · have p3869_0 := h3869c.1
                                                        have p3869_1 := h3869c.2.1
                                                        have p3869_2 := h3869c.2.2.1
                                                        have p3869_3 := h3869c.2.2.2
                                                        linarith only [hlam, p3869_0]
                                                    · linarith only [h3609, h3610, h3827, h3867, hc34, hlam, ht01, ht12, ht23]
                                                    · rcases h2bigk with h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h0, hlam, p3963_1]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        rcases p3963_3 (m.d 0 2) (by simp) with h3966 | h3966
                                                        · rcases p3963_3 (m.d 1 2) (by simp) with h3967 | h3967
                                                          · rcases p3963_3 (m.d 2 3) (by simp) with h3968 | h3968
                                                            · linarith only [h3968, hlam, p3963_0]
                                                            · rcases p3963_3 (m.d 2 4) (by simp) with h3970 | h3970
                                                              · linarith only [h3818, h3970, hlam]
                                                              · linarith only [h3831, h3970, hlam]
                                                          · linarith only [h3824, h3967, hlam]
                                                        · linarith only [h3966, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        rcases p3963_3 (m.d 0 2) (by simp) with h3975 | h3975
                                                        · rcases p3963_3 (m.d 1 2) (by simp) with h3976 | h3976
                                                          · rcases p3963_3 (m.d 2 3) (by simp) with h3977 | h3977
                                                            · linarith only [h3817, h3977, hlam]
                                                            · rcases p3963_3 (m.d 2 4) (by simp) with h3979 | h3979
                                                              · linarith only [h3979, hlam, p3963_0]
                                                              · rcases p3963_3 (m.d 2 5) (by simp) with h3981 | h3981
                                                                · linarith only [h3819, h3981, hlam]
                                                                · rcases h3bigk with h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c | h3983c
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3609, h3610, h3827, hc13, hc34, hlam, hphi, p3983_1]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3609, h3610, h3827, h3833, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3983_1]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3820, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    rcases p3983_3 (m.d 0 3) (by simp) with h3988 | h3988
                                                                    · rcases p3983_3 (m.d 1 3) (by simp) with h3989 | h3989
                                                                      · linarith only [h3609, h3989, hlam]
                                                                      · linarith only [h3829, h3989, hlam]
                                                                    · linarith only [h3988, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3609, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3609, h3610, h3827, h3833, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3983_1]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3827, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3609, h3610, h3827, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3983_1]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3817, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3824, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3831, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3609, h3610, h3824, h3827, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3983_1]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3836_1, p3983_1]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    rcases p3983_3 (m.d 0 3) (by simp) with h4004 | h4004
                                                                    · linarith only [h3820, h4004, hlam]
                                                                    · linarith only [h3609, h4004, hlam]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    rcases p3983_3 (m.d 0 3) (by simp) with h4007 | h4007
                                                                    · linarith only [h3820, h4007, hlam]
                                                                    · linarith only [h3817, h4007, hlam]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3609, h3610, h3816, h3826, h3827, h3833, hlam, p3836_1, p3983_2]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3822, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3829, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3833, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [h3835, hlam, p3983_0]
                                                                  · have p3983_0 := h3983c.1
                                                                    have p3983_1 := h3983c.2.1
                                                                    have p3983_2 := h3983c.2.2.1
                                                                    have p3983_3 := h3983c.2.2.2
                                                                    linarith only [hlam, p3983_0]
                                                          · linarith only [h3825, h3976, hlam]
                                                        · linarith only [h3975, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        rcases p3963_3 (m.d 0 2) (by simp) with h4019 | h4019
                                                        · rcases p3963_3 (m.d 1 2) (by simp) with h4020 | h4020
                                                          · rcases p3963_3 (m.d 2 3) (by simp) with h4021 | h4021
                                                            · linarith only [h3817, h4021, hlam]
                                                            · linarith only [h3833, h4021, hlam]
                                                          · linarith only [h3826, h4020, hlam]
                                                        · linarith only [h4019, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h0, h3609, h3816, h3826, h3833, h3835, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3836_1, p3963_1]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        rcases p3963_3 (m.d 0 2) (by simp) with h4028 | h4028
                                                        · linarith only [h0, h4028, hlam]
                                                        · linarith only [h3817, h4028, hlam]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        rcases p3963_3 (m.d 0 2) (by simp) with h4031 | h4031
                                                        · linarith only [h0, h4031, hlam]
                                                        · linarith only [h3818, h4031, hlam]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h0, h3609, h3816, h3826, hlam, p3836_1, p3963_2]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h3817, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h3824, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h3831, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h3609, h3610, h3824, h3827, h3833, h3835, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3963_1]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h3818, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h3825, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h0, h3818, h3833, h3835, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3963_1]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        rcases p3963_3 (m.d 0 2) (by simp) with h4044 | h4044
                                                        · rcases p3963_3 (m.d 1 2) (by simp) with h4045 | h4045
                                                          · rcases p3963_3 (m.d 2 3) (by simp) with h4046 | h4046
                                                            · linarith only [h3831, h4046, hlam]
                                                            · linarith only [h3833, h4046, hlam]
                                                          · linarith only [h3826, h4045, hlam]
                                                        · linarith only [h3819, h4044, hlam]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h3819, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h3826, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h3833, hlam, p3963_1]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [h3834, hlam, p3963_0]
                                                      · have p3963_0 := h3963c.1
                                                        have p3963_1 := h3963c.2.1
                                                        have p3963_2 := h3963c.2.2.1
                                                        have p3963_3 := h3963c.2.2.2
                                                        linarith only [hlam, p3963_0]
                                                    · linarith only [h3867, hc03, hlam, p3836_1]
                                                · linarith only [h3823, h3864, hlam]
                                              · linarith only [h3822, h3863, hlam]
                                            · linarith only [h3819, h3862, hlam]
                                          · linarith only [h3816, h3861, hlam]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3609, h3610, h3827, hc13, hc34, hlam, hphi, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3818, hlam, p3836_0]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          rcases p3836_3 (m.d 0 1) (by simp) with h4063 | h4063
                                          · linarith only [h3610, h4063, hlam]
                                          · linarith only [h3609, h4063, hlam]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [hlam, p3836_0]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          rcases p3836_3 (m.d 0 1) (by simp) with h4067 | h4067
                                          · linarith only [h3610, h4067, hlam]
                                          · linarith only [h3816, h4067, hlam]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3816, hlam, p3836_0]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3819, hlam, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3822, hlam, p3836_0]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [h3823, hlam, p3836_1]
                                        · have p3836_0 := h3836c.1
                                          have p3836_1 := h3836c.2.1
                                          have p3836_2 := h3836c.2.2.1
                                          have p3836_3 := h3836c.2.2.2
                                          linarith only [hlam, p3836_0]
                                      · linarith only [h3610, h3827, h3835, hc04, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h3830, h3834, hc24, hlam, hphi, ht45, u5elo1]
                                  · linarith only [h3833, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h3609, h3610, h3830, hc13, hc45, hlam, hphi, ht34]
                            · linarith only [h3824, h3829, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h3826, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h3609, h3818, h3824, h3825, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h3817, h3824, hlam]
                  · linarith only [h3610, h3823, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h3822, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h3819, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4086 | h4086
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4087 | h4087
              · linarith only [h0, h3609, h3818, h4087, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4089 | h4089
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4090 | h4090
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4091 | h4091
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4092 | h4092
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4093 | h4093
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4094 | h4094
                          · linarith only [h0, h3609, h3818, h4087, h4092, h4094, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4096 | h4096
                            · linarith only [h0, h3609, h3818, h4092, h4096, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h4091, h4096, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h3818, h4092, h4093, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4100 | h4100
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4101 | h4101
                          · linarith only [h0, h3609, h4087, h4092, h4101, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4103 | h4103
                            · linarith only [h0, h3609, h4092, h4103, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h4091, h4103, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h3609, h4091, h4100, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h0, h3609, h3817, h3818, h4091, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h4090, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h4089, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h4086, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h3609, h3817, hlam]
      · linarith only [h3609, h3816, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s5 m hb0 hb2 hb3 hb5 h0 h3609

set_option maxHeartbeats 13694000 in
set_option maxHeartbeats 13694000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s4 m hb0 hb2 hb3 hb5 h0

end R2N4
