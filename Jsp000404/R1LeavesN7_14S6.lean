import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9218000 in
set_option maxHeartbeats 9218000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3600 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h3601 | h3601
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3602 | h3602
    · linarith only [h0, h1, h3602, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3604 | h3604
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3605 | h3605
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3606 | h3606
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3607 | h3607
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3608 | h3608
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3609 | h3609
                · linarith only [h0, h1, h3602, h3604, h3609, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3611 | h3611
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3612 | h3612
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3613 | h3613
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3614 | h3614
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3615 | h3615
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3616 | h3616
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3617 | h3617
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3618 | h3618
                                · linarith only [h0, h1, h3609, h3611, h3618, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h1, h3609, h3611, h3615, h3618, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h1, h3609, h3617, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h3609, h3616, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3623 | h3623
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3624 | h3624
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3625 | h3625
                                · linarith only [h3611, h3615, h3625, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3627 | h3627
                                  · linarith only [h3611, h3615, h3623, h3627, hlam]
                                  · rcases h0bigk with h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c | h3629c
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3604, h3608, h3611, h3615, h3623, hc34, hlam, hphi, ht0b, ht45, ht5b, p3629_1, u0elo0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h1, hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h1, h3608, h3609, h3611, h3615, h3623, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3629_1]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h1, h3608, h3609, h3611, h3615, h3623, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3629_1]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h0, hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3602, hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3608, h3611, h3615, h3623, hc34, hlam, hphi, ht0b, ht45, ht5b, p3629_1, u0elo1]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h0, h1, h3608, h3609, h3611, h3615, h3623, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3629_1]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3629_1, u0elo2]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h0, h3612, h3624, hc35, hlam, hphi, ht0b, ht5b, p3629_1, u0elo2]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3608, h3611, h3615, h3623, hc34, hlam, hphi, ht0b, ht45, ht5b, p3629_1, u0elo2]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3608, h3611, h3615, h3623, hc34, hlam, hphi, ht0b, ht45, ht5b, p3629_1, u0elo2]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3600, hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3604, hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3606, hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3608, h3611, h3615, h3623, hc34, hlam, hphi, ht0b, ht45, ht5b, p3629_1, u0elo3]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3601, hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3605, hlam, p3629_1]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3607, hlam, p3629_0]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [h3608, hlam, p3629_1]
                                    · have p3629_0 := h3629c.1
                                      have p3629_1 := h3629c.2.1
                                      have p3629_2 := h3629c.2.2.1
                                      have p3629_3 := h3629c.2.2.2
                                      linarith only [hlam, p3629_0]
                              · linarith only [h0, h1, h3609, h3611, h3623, h3624, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h3604, h3608, h3609, h3615, h3623, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h3611, h3614, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h3611, h3613, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h3605, h3611, h3612, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h3604, h3609, h3611, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3661 | h3661
                · linarith only [h0, h3602, h3661, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3663 | h3663
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3664 | h3664
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3665 | h3665
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3666 | h3666
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3667 | h3667
                          · linarith only [h1, h3600, h3608, h3661, h3667, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3669 | h3669
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3670 | h3670
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3671 | h3671
                                · linarith only [h3604, h3608, h3671, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3673 | h3673
                                  · linarith only [h3600, h3608, h3663, h3669, h3673, hlam]
                                  · rcases h0bigk with h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h1, h3661, hc02, hc23, hlam, hphi, p3675_1]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h1, hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      rcases p3675_3 (m.d 0 1) (by simp) with h3679 | h3679
                                      · rcases p3675_3 (m.d 0 2) (by simp) with h3680 | h3680
                                        · linarith only [h0, h3680, hlam]
                                        · linarith only [h3604, h3680, hlam]
                                      · linarith only [h3600, h3679, hlam]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      rcases p3675_3 (m.d 0 1) (by simp) with h3684 | h3684
                                      · rcases p3675_3 (m.d 0 2) (by simp) with h3685 | h3685
                                        · linarith only [h0, h3685, hlam]
                                        · linarith only [h3605, h3685, hlam]
                                      · linarith only [h3601, h3684, hlam]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h0, hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h3602, hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      rcases p3675_3 (m.d 0 1) (by simp) with h3692 | h3692
                                      · rcases p3675_3 (m.d 0 2) (by simp) with h3693 | h3693
                                        · rcases p3675_3 (m.d 0 3) (by simp) with h3694 | h3694
                                          · rcases p3675_3 (m.d 0 4) (by simp) with h3695 | h3695
                                            · linarith only [h3604, h3695, hlam]
                                            · rcases p3675_3 (m.d 0 5) (by simp) with h3697 | h3697
                                              · linarith only [h3605, h3697, hlam]
                                              · linarith only [h3608, h3697, hlam]
                                          · linarith only [h3606, h3694, hlam]
                                        · linarith only [h3604, h3693, hlam]
                                      · linarith only [h3600, h3692, hlam]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      rcases p3675_3 (m.d 0 1) (by simp) with h3703 | h3703
                                      · rcases p3675_3 (m.d 0 2) (by simp) with h3704 | h3704
                                        · rcases p3675_3 (m.d 0 3) (by simp) with h3705 | h3705
                                          · rcases p3675_3 (m.d 0 4) (by simp) with h3706 | h3706
                                            · linarith only [h3604, h3706, hlam]
                                            · rcases p3675_3 (m.d 0 5) (by simp) with h3708 | h3708
                                              · linarith only [h3605, h3708, hlam]
                                              · rcases h2bigk with h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c | h3710c
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h0, h1, h3661, h3664, h3669, h3671, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3710_1]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h3602, hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  rcases p3710_3 (m.d 0 2) (by simp) with h3714 | h3714
                                                  · rcases p3710_3 (m.d 1 2) (by simp) with h3715 | h3715
                                                    · linarith only [h0, h3715, hlam]
                                                    · linarith only [h3663, h3715, hlam]
                                                  · linarith only [h3714, hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  rcases p3710_3 (m.d 0 2) (by simp) with h3719 | h3719
                                                  · rcases p3710_3 (m.d 1 2) (by simp) with h3720 | h3720
                                                    · linarith only [h0, h3720, hlam]
                                                    · linarith only [h3664, h3720, hlam]
                                                  · linarith only [h3719, hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h0, hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h3661, hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h0, h1, h3661, h3669, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3710_1]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h0, h1, h3661, h3669, h3671, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3710_1]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h3600, h3608, h3663, h3669, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3675_1, p3710_1]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  rcases p3710_3 (m.d 0 2) (by simp) with h3730 | h3730
                                                  · linarith only [h3602, h3730, hlam]
                                                  · linarith only [h0, h3730, hlam]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h0, h1, h3600, h3608, h3661, h3663, hlam, p3675_1, p3710_2]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h0, h1, h3605, h3661, hlam, p3675_1, p3710_2]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h3604, hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h3663, hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h3669, hlam, p3710_1]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h3671, hlam, p3710_1]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h3605, hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h3664, hlam, p3710_0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h3670, hlam, p3710_1]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [h0, h3601, h3664, h3669, hc34, hlam, hphi, ht0b, ht45, ht5b, p3675_1, p3710_1, u0elo0]
                                                · have p3710_0 := h3710c.1
                                                  have p3710_1 := h3710c.2.1
                                                  have p3710_2 := h3710c.2.2.1
                                                  have p3710_3 := h3710c.2.2.2
                                                  linarith only [hlam, p3710_0]
                                          · linarith only [h3607, h3705, hlam]
                                        · linarith only [h3605, h3704, hlam]
                                      · linarith only [h3601, h3703, hlam]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3675_1, u0elo2]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h3604, h3669, hc34, hlam, hphi, ht0b, ht45, ht5b, p3675_1, u0elo2]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      rcases p3675_3 (m.d 0 1) (by simp) with h3752 | h3752
                                      · linarith only [h1, h3752, hlam]
                                      · linarith only [h3600, h3752, hlam]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      rcases p3675_3 (m.d 0 1) (by simp) with h3755 | h3755
                                      · linarith only [h1, h3755, hlam]
                                      · linarith only [h3601, h3755, hlam]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h3600, hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h3604, hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h3606, hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h3608, hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h3601, hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h3605, hlam, p3675_1]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [h3607, hlam, p3675_0]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      rcases p3675_3 (m.d 0 1) (by simp) with h3766 | h3766
                                      · rcases p3675_3 (m.d 0 2) (by simp) with h3767 | h3767
                                        · rcases p3675_3 (m.d 0 3) (by simp) with h3768 | h3768
                                          · rcases p3675_3 (m.d 0 4) (by simp) with h3769 | h3769
                                            · linarith only [h3608, h3769, hlam]
                                            · rcases p3675_3 (m.d 0 5) (by simp) with h3771 | h3771
                                              · rcases h2bigk with h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3664, hc25, hlam, hphi, ht0b, ht5b, p3772_1, u0elo1]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3602, hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  rcases p3772_3 (m.d 0 2) (by simp) with h3776 | h3776
                                                  · rcases p3772_3 (m.d 1 2) (by simp) with h3777 | h3777
                                                    · linarith only [h0, h3777, hlam]
                                                    · linarith only [h3663, h3777, hlam]
                                                  · linarith only [h3776, hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  rcases p3772_3 (m.d 0 2) (by simp) with h3781 | h3781
                                                  · rcases p3772_3 (m.d 1 2) (by simp) with h3782 | h3782
                                                    · linarith only [h0, h3782, hlam]
                                                    · linarith only [h3664, h3782, hlam]
                                                  · linarith only [h3781, hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h0, hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3661, hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h0, h1, h3661, h3669, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3772_1]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h0, h1, h3661, h3669, h3671, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3772_1]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3600, h3605, h3663, h3669, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3675_1, p3772_1]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  rcases p3772_3 (m.d 0 2) (by simp) with h3792 | h3792
                                                  · linarith only [h3602, h3792, hlam]
                                                  · linarith only [h0, h3792, hlam]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h0, h1, h3600, h3605, h3661, h3663, hlam, p3675_1, p3772_2]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h0, h1, h3661, h3664, hlam, p3772_2]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3604, hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3663, hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3669, hlam, p3772_1]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3671, hlam, p3772_1]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3605, hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3664, hlam, p3772_0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h3670, hlam, p3772_1]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [h0, h3664, h3669, hc34, hlam, hphi, ht0b, ht45, ht5b, p3772_1, u0elo0]
                                                · have p3772_0 := h3772c.1
                                                  have p3772_1 := h3772c.2.1
                                                  have p3772_2 := h3772c.2.2.1
                                                  have p3772_3 := h3772c.2.2.2
                                                  linarith only [hlam, p3772_0]
                                              · linarith only [h3608, h3771, hlam]
                                          · linarith only [h3606, h3768, hlam]
                                        · linarith only [h3604, h3767, hlam]
                                      · linarith only [h3600, h3766, hlam]
                                    · have p3675_0 := h3675c.1
                                      have p3675_1 := h3675c.2.1
                                      have p3675_2 := h3675c.2.2.1
                                      have p3675_3 := h3675c.2.2.2
                                      linarith only [hlam, p3675_0]
                              · linarith only [h0, h1, h3661, h3670, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h3661, h3663, h3669, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h3663, h3666, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h3663, h3665, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h3605, h3663, h3664, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h3604, h3661, h3663, hc12, hc23, hlam, hphi]
            · linarith only [h0, h1, h3605, h3607, hlam]
          · linarith only [h1, h3600, h3606, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3821 | h3821
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3822 | h3822
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3823 | h3823
              · linarith only [h3604, h3605, h3823, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3825 | h3825
                · linarith only [h0, h1, h3602, h3825, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3827 | h3827
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3828 | h3828
                    · linarith only [h0, h3605, h3828, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3830 | h3830
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3831 | h3831
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3832 | h3832
                          · linarith only [h1, h3600, h3823, h3825, h3832, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3834 | h3834
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3835 | h3835
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3836 | h3836
                                · linarith only [h1, h3600, h3601, h3823, h3825, h3827, h3828, h3836, hc12, hc23, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3838 | h3838
                                  · linarith only [h3604, h3605, h3834, h3836, h3838, hlam]
                                  · rcases h0bigk with h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h1, h3825, hc02, hc23, hlam, hphi, p3840_1]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h1, hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      rcases p3840_3 (m.d 0 1) (by simp) with h3844 | h3844
                                      · rcases p3840_3 (m.d 0 2) (by simp) with h3845 | h3845
                                        · linarith only [h0, h3845, hlam]
                                        · linarith only [h3604, h3845, hlam]
                                      · linarith only [h3600, h3844, hlam]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h0, h1, h3605, h3825, h3827, h3834, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3840_1]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h0, hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h3602, hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h3600, h3605, h3836, hc14, hc45, hlam, hphi, p3840_1]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h3605, hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h0, h3827, h3834, hc34, hlam, hphi, ht0b, ht45, ht5b, p3840_1, u0elo2]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h0, h3827, h3834, hc34, hlam, hphi, ht0b, ht45, ht5b, p3840_1, u0elo2]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      rcases p3840_3 (m.d 0 1) (by simp) with h3858 | h3858
                                      · linarith only [h1, h3858, hlam]
                                      · linarith only [h3600, h3858, hlam]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h0, h3605, h3827, h3834, hc34, hlam, hphi, ht0b, ht45, ht5b, p3840_1, u0elo2]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h3600, hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h3604, hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h3821, hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h3823, hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h3601, hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h0, h3827, h3834, hc34, hlam, hphi, ht0b, ht45, ht5b, p3840_1, u0elo4]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [h3822, hlam, p3840_0]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      rcases p3840_3 (m.d 0 1) (by simp) with h3870 | h3870
                                      · rcases p3840_3 (m.d 0 2) (by simp) with h3871 | h3871
                                        · linarith only [h3605, h3871, hlam]
                                        · linarith only [h3604, h3871, hlam]
                                      · linarith only [h3600, h3870, hlam]
                                    · have p3840_0 := h3840c.1
                                      have p3840_1 := h3840c.2.1
                                      have p3840_2 := h3840c.2.2.1
                                      have p3840_3 := h3840c.2.2.2
                                      linarith only [hlam, p3840_0]
                              · linarith only [h0, h1, h3825, h3827, h3834, h3835, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h3825, h3834, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h1, h3601, h3827, h3828, h3831, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1, h3601, h3827, h3828, h3830, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h3604, h3605, h3827, hc12, hc25, hlam, hphi]
            · linarith only [h1, h3601, h3822, hlam]
          · linarith only [h1, h3600, h3821, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3883 | h3883
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3884 | h3884
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3885 | h3885
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3886 | h3886
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3887 | h3887
                · linarith only [h0, h3602, h3887, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3889 | h3889
                  · linarith only [h0, h3604, h3889, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3891 | h3891
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3892 | h3892
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3893 | h3893
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3894 | h3894
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3895 | h3895
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3896 | h3896
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3897 | h3897
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3898 | h3898
                                  · rcases h0bigk with h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h1, h3887, hc02, hc23, hlam, hphi, p3899_1]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h1, hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h0, h1, h3604, h3887, hc12, hc23, hlam, hphi, p3899_1]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      rcases p3899_3 (m.d 0 1) (by simp) with h3904 | h3904
                                      · rcases p3899_3 (m.d 0 2) (by simp) with h3905 | h3905
                                        · linarith only [h0, h3905, hlam]
                                        · linarith only [h3883, h3905, hlam]
                                      · linarith only [h3601, h3904, hlam]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h0, hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3602, hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3604, hlam, p3899_1]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      rcases p3899_3 (m.d 0 1) (by simp) with h3913 | h3913
                                      · rcases p3899_3 (m.d 0 2) (by simp) with h3914 | h3914
                                        · rcases p3899_3 (m.d 0 3) (by simp) with h3915 | h3915
                                          · rcases p3899_3 (m.d 0 4) (by simp) with h3916 | h3916
                                            · rcases p3899_3 (m.d 0 5) (by simp) with h3917 | h3917
                                              · linarith only [h3883, h3917, hlam]
                                              · rcases h2bigk with h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c | h3919c
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3891, h3896, h3898, hc45, hlam, hphi, ht0b, ht5b, p3919_1, u0elo1]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3602, hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3604, hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  rcases p3919_3 (m.d 0 2) (by simp) with h3924 | h3924
                                                  · rcases p3919_3 (m.d 1 2) (by simp) with h3925 | h3925
                                                    · linarith only [h0, h3925, hlam]
                                                    · linarith only [h3891, h3925, hlam]
                                                  · linarith only [h3924, hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h0, hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3887, hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3889, hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h0, h1, h3887, h3896, h3898, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3919_1]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3601, h3891, h3896, h3898, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3899_1, p3919_1]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  rcases p3919_3 (m.d 0 2) (by simp) with h3935 | h3935
                                                  · linarith only [h3602, h3935, hlam]
                                                  · linarith only [h0, h3935, hlam]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3601, h3604, h3891, h3896, h3898, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3899_1, p3919_1]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h0, h1, h3601, h3887, h3891, hlam, p3899_1, p3919_2]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3899_1, p3919_1]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  rcases p3919_3 (m.d 0 2) (by simp) with h3942 | h3942
                                                  · linarith only [h3604, h3942, hlam]
                                                  · linarith only [h0, h3942, hlam]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3895, hlam, p3919_1]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3601, h3604, h3891, hlam, p3899_1, p3919_2]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3883, hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3891, hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3896, hlam, p3919_1]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [h3897, hlam, p3919_0]
                                                · have p3919_0 := h3919c.1
                                                  have p3919_1 := h3919c.2.1
                                                  have p3919_2 := h3919c.2.2.1
                                                  have p3919_3 := h3919c.2.2.2
                                                  linarith only [hlam, p3919_0]
                                            · linarith only [h3886, h3916, hlam]
                                          · linarith only [h3885, h3915, hlam]
                                        · linarith only [h3883, h3914, hlam]
                                      · linarith only [h3601, h3913, hlam]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3600, h3889, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3899_1, u0elo2]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3883, h3896, h3898, hc45, hlam, hphi, ht0b, ht5b, p3899_1, u0elo2]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3604, h3883, h3896, h3898, hc45, hlam, hphi, ht0b, ht5b, p3899_1, u0elo2]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      rcases p3899_3 (m.d 0 1) (by simp) with h3961 | h3961
                                      · linarith only [h1, h3961, hlam]
                                      · linarith only [h3601, h3961, hlam]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3600, hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h0, h3891, h3896, h3898, hc45, hlam, hphi, ht0b, ht5b, p3899_1, u0elo3]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3884, hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      rcases p3899_3 (m.d 0 1) (by simp) with h3968 | h3968
                                      · rcases p3899_3 (m.d 0 2) (by simp) with h3969 | h3969
                                        · linarith only [h3604, h3969, hlam]
                                        · linarith only [h3883, h3969, hlam]
                                      · linarith only [h3601, h3968, hlam]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3601, hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3883, hlam, p3899_1]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3885, hlam, p3899_0]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [h3886, hlam, p3899_1]
                                    · have p3899_0 := h3899c.1
                                      have p3899_1 := h3899c.2.1
                                      have p3899_2 := h3899c.2.2.1
                                      have p3899_3 := h3899c.2.2.2
                                      linarith only [hlam, p3899_0]
                                  · linarith only [h1, h3600, h3887, h3894, h3898, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h3601, h3604, h3891, h3894, h3897, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                              · linarith only [h1, h3600, h3887, h3889, h3891, h3896, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h3600, h3887, h3889, h3891, h3895, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h3600, h3886, h3889, h3891, h3894, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h1, h3891, h3893, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h3600, h3889, h3891, h3892, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h3604, h3883, h3891, hc12, hc24, hlam, hphi]
              · linarith only [h3604, h3883, h3886, hlam]
            · linarith only [h1, h3600, h3604, h3883, h3885, hlam]
          · linarith only [h1, h3600, h3884, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3989 | h3989
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3990 | h3990
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3991 | h3991
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3992 | h3992
                · linarith only [h0, h3602, h3992, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3994 | h3994
                  · linarith only [h0, h3604, h3994, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3996 | h3996
                    · linarith only [h0, h3883, h3996, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3998 | h3998
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3999 | h3999
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4000 | h4000
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4001 | h4001
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4002 | h4002
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4003 | h4003
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4004 | h4004
                                  · rcases h0bigk with h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c | h4005c
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h1, h3992, hc02, hc23, hlam, hphi, p4005_1]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h1, hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h1, h3600, h3992, h3998, h4004, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4005_1]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h0, h1, h3883, h3992, hc12, hc23, hlam, hphi, p4005_1]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h0, hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h3602, hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h3604, hlam, p4005_1]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h3883, hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4005_1, u0elo2]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      rcases p4005_3 (m.d 0 1) (by simp) with h4017 | h4017
                                      · linarith only [h1, h4017, hlam]
                                      · linarith only [h0, h4017, hlam]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h3600, h3998, h4004, hc45, hlam, hphi, ht0b, ht5b, p4005_1, u0elo2]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      rcases p4005_3 (m.d 0 1) (by simp) with h4022 | h4022
                                      · linarith only [h1, h4022, hlam]
                                      · linarith only [h3601, h4022, hlam]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h3600, hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h0, h1, h3600, h3992, hc12, hc23, hlam, hphi, p4005_1]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h3989, hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h0, h1, h3600, h3883, h3992, hc12, hc23, hlam, hphi, p4005_1]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h3601, hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h0, h1, h3601, h3992, hc12, hc23, hlam, hphi, p4005_1]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h3990, hlam, p4005_0]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [h3991, hlam, p4005_1]
                                    · have p4005_0 := h4005c.1
                                      have p4005_1 := h4005c.2.1
                                      have p4005_2 := h4005c.2.2.1
                                      have p4005_3 := h4005c.2.2.2
                                      linarith only [hlam, p4005_0]
                                  · linarith only [h1, h3600, h3992, h4000, h4004, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1, h3600, h3604, h3992, h4000, h4003, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h1, h3992, h4002, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h3600, h3992, h4000, h4001, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h3600, h3991, h3992, h3994, h4000, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h3999, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h3600, h3994, h3998, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4042 | h4042
                · linarith only [h0, h3602, h4042, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4044 | h4044
                  · linarith only [h0, h3604, h4044, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4046 | h4046
                    · linarith only [h0, h3883, h4046, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4048 | h4048
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4049 | h4049
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4050 | h4050
                          · linarith only [h3600, h3991, h4050, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4052 | h4052
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4053 | h4053
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4054 | h4054
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4055 | h4055
                                  · linarith only [h3600, h3991, h4048, h4055, hlam]
                                  · rcases h0bigk with h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c | h4057c
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h1, h4042, hc02, hc23, hlam, hphi, p4057_1]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h1, hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h0, h1, h3604, h4042, hc12, hc23, hlam, hphi, p4057_1]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h0, h1, h3883, h4042, hc12, hc23, hlam, hphi, p4057_1]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h0, hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h3602, hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h3604, hlam, p4057_1]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h3883, hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4057_1, u0elo2]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      rcases p4057_3 (m.d 0 1) (by simp) with h4069 | h4069
                                      · linarith only [h1, h4069, hlam]
                                      · linarith only [h0, h4069, hlam]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      rcases p4057_3 (m.d 0 1) (by simp) with h4073 | h4073
                                      · linarith only [h1, h4073, hlam]
                                      · linarith only [h3600, h4073, hlam]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      rcases p4057_3 (m.d 0 1) (by simp) with h4076 | h4076
                                      · linarith only [h1, h4076, hlam]
                                      · linarith only [h3601, h4076, hlam]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h3600, hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h0, h3991, h4054, hc12, hc24, hlam, hphi, p4057_1]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h3989, hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h3991, hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h3601, hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h0, h1, h3601, h4042, hc12, hc23, hlam, hphi, p4057_1]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h3990, hlam, p4057_0]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [h0, h1, h3601, h3604, h4042, hc12, hc23, hlam, hphi, p4057_1]
                                    · have p4057_0 := h4057c.1
                                      have p4057_1 := h4057c.2.1
                                      have p4057_2 := h4057c.2.2.1
                                      have p4057_3 := h4057c.2.2.2
                                      linarith only [hlam, p4057_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4089 | h4089
                                  · linarith only [h1, h3600, h4042, h4048, h4054, h4089, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases h0bigk with h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h0, h1, h4042, hc12, hc23, hlam, hphi, p4091_1]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h1, hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h0, h1, h3604, h4042, hc12, hc23, hlam, hphi, p4091_1]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h0, h1, h3883, h4042, hc12, hc23, hlam, hphi, p4091_1]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h0, hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h3602, hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h3604, hlam, p4091_1]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h3883, hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4091_1, u0elo2]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      rcases p4091_3 (m.d 0 1) (by simp) with h4103 | h4103
                                      · linarith only [h1, h4103, hlam]
                                      · linarith only [h0, h4103, hlam]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      rcases p4091_3 (m.d 0 1) (by simp) with h4107 | h4107
                                      · linarith only [h1, h4107, hlam]
                                      · linarith only [h3600, h4107, hlam]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      rcases p4091_3 (m.d 0 1) (by simp) with h4110 | h4110
                                      · linarith only [h1, h4110, hlam]
                                      · linarith only [h3601, h4110, hlam]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h3600, hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h0, h1, h3600, h4042, hc12, hc23, hlam, hphi, p4091_1]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h3989, hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h3991, hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h3601, hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h0, h1, h3601, h4042, hc12, hc23, hlam, hphi, p4091_1]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h3990, hlam, p4091_0]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [h0, h1, h3601, h3604, h4042, hc12, hc23, hlam, hphi, p4091_1]
                                    · have p4091_0 := h4091c.1
                                      have p4091_1 := h4091c.2.1
                                      have p4091_2 := h4091c.2.2.1
                                      have p4091_3 := h4091c.2.2.2
                                      linarith only [hlam, p4091_0]
                              · linarith only [h1, h3601, h4042, h4049, h4053, hlam]
                            · linarith only [h1, h3600, h3601, h4042, h4048, h4052, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h1, h3600, h4044, h4049, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h3600, h4044, h4048, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h3601, h3990, hlam]
          · linarith only [h1, h3600, h3989, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4129 | h4129
    · linarith only [h0, h1, h4129, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4131 | h4131
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4132 | h4132
        · linarith only [h0, h3601, h4132, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4134 | h4134
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4135 | h4135
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4136 | h4136
              · linarith only [h0, h3601, h4131, h4136, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4138 | h4138
                · linarith only [h0, h4129, h4138, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4140 | h4140
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4141 | h4141
                    · linarith only [h0, h3601, h4132, h4141, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4143 | h4143
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4144 | h4144
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4145 | h4145
                          · linarith only [h0, h4136, h4140, h4145, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h3601, h4140, h4145, hc24, hc45, hlam, hphi]
                        · linarith only [h0, h1, h4135, h4140, h4144, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1, h4140, h4143, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h4129, h4131, h4140, hc12, hc23, hlam, hphi]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4151 | h4151
              · linarith only [h0, h3601, h4131, h4151, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4153 | h4153
                · linarith only [h0, h1, h4135, h4153, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4155 | h4155
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4156 | h4156
                    · linarith only [h0, h1, h4132, h4135, h4156, hc02, hc35, hlam, hphi, ht23]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4158 | h4158
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4159 | h4159
                        · linarith only [h0, h1, h4135, h4155, h4159, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1, h4155, h4159, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h4155, h4158, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h4129, h4131, h4155, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h4131, h4134, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4165 | h4165
        · linarith only [h3600, h3601, h4131, h4165, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4167 | h4167
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4168 | h4168
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4169 | h4169
              · linarith only [h3600, h3601, h4169, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4171 | h4171
                · linarith only [h0, h4129, h4171, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4173 | h4173
                  · linarith only [h0, h4131, h4173, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4175 | h4175
                    · linarith only [h0, h3601, h4165, h4175, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4177 | h4177
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4178 | h4178
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4179 | h4179
                          · linarith only [h3600, h4131, h4169, h4179, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4181 | h4181
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4182 | h4182
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4183 | h4183
                                · linarith only [h0, h3601, h4179, h4181, h4183, hc12, hc23, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4185 | h4185
                                  · linarith only [h3600, h4177, h4183, h4185, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · rcases h0bigk with h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c | h4187c
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h3601, h4175, h4183, hc02, hc45, hlam, hphi, ht23, ht34, p4187_1]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h1, hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h0, h3601, h4131, h4175, h4183, hc12, hc45, hlam, hphi, ht23, ht34, p4187_1]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h3601, hlam, p4187_1]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h0, hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h4129, hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h4131, hlam, p4187_1]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h4165, hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h3600, hc14, hlam, hphi, ht0b, ht45, ht5b, p4187_1, u0elo2]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      rcases p4187_3 (m.d 0 1) (by simp) with h4199 | h4199
                                      · linarith only [h1, h4199, hlam]
                                      · linarith only [h0, h4199, hlam]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      rcases p4187_3 (m.d 0 1) (by simp) with h4203 | h4203
                                      · linarith only [h1, h4203, hlam]
                                      · linarith only [h3600, h4203, hlam]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h3600, h3601, h4173, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4187_1, u0elo2]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h3600, hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h0, h1, h3600, h4171, hc12, hc23, hlam, hphi, p4187_1]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h4167, hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h4169, hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4187_1, u0elo4]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      rcases p4187_3 (m.d 0 1) (by simp) with h4213 | h4213
                                      · linarith only [h3601, h4213, hlam]
                                      · linarith only [h0, h4213, hlam]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [h4168, hlam, p4187_0]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      rcases p4187_3 (m.d 0 1) (by simp) with h4217 | h4217
                                      · linarith only [h3601, h4217, hlam]
                                      · linarith only [h3600, h4217, hlam]
                                    · have p4187_0 := h4187c.1
                                      have p4187_1 := h4187c.2.1
                                      have p4187_2 := h4187c.2.2.1
                                      have p4187_3 := h4187c.2.2.2
                                      linarith only [hlam, p4187_0]
                              · linarith only [h1, h3600, h4168, h4171, h4173, h4182, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h3600, h3601, h4171, h4173, h4178, h4181, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h1, h4168, h4178, hlam]
                      · linarith only [h1, h3600, h4173, h4177, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4225 | h4225
              · linarith only [h3600, h3601, h4225, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4227 | h4227
                · linarith only [h0, h1, h4129, h4227, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4229 | h4229
                  · linarith only [h0, h4131, h4229, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4231 | h4231
                    · linarith only [h0, h4165, h4231, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4233 | h4233
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4234 | h4234
                        · linarith only [h0, h1, h4168, h4227, h4234, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h3600, h4229, h4234, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h3600, h4229, h4233, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1, h3600, h4167, hlam]

end R2N4
