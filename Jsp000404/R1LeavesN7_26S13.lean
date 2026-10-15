import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2760 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3404 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3607 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3608 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3609 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h3610 | h3610
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3611 | h3611
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3612 | h3612
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3613 | h3613
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3614 | h3614
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3615 | h3615
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3616 | h3616
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3617 | h3617
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3618 | h3618
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3619 | h3619
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3620 | h3620
                      · linarith only [h3607, h3617, h3620, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h3608, h3619, h3620, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3623 | h3623
                      · linarith only [h3617, h3619, h3623, hlam]
                      · rcases h3bigk with h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h2760, hlam, p3625_1]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h2760, h3612, h3617, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3625_1, u4ehi3]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          rcases p3625_3 (m.d 0 3) (by simp) with h3629 | h3629
                          · rcases p3625_3 (m.d 1 3) (by simp) with h3630 | h3630
                            · rcases p3625_3 (m.d 2 3) (by simp) with h3631 | h3631
                              · linarith only [h3607, h3631, hlam]
                              · linarith only [h3617, h3631, hlam]
                            · linarith only [h3614, h3630, hlam]
                          · linarith only [h3629, hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          rcases p3625_3 (m.d 0 3) (by simp) with h3636 | h3636
                          · rcases p3625_3 (m.d 1 3) (by simp) with h3637 | h3637
                            · rcases p3625_3 (m.d 2 3) (by simp) with h3638 | h3638
                              · linarith only [h3607, h3638, hlam]
                              · linarith only [h3618, h3638, hlam]
                            · linarith only [h3615, h3637, hlam]
                          · linarith only [h3636, hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3607, h3612, h3618, h3623, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3625_1, u4ehi3]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3612, h3618, h3623, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3625_1, u4ehi3]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          rcases p3625_3 (m.d 0 3) (by simp) with h3646 | h3646
                          · linarith only [h2760, h3646, hlam]
                          · linarith only [h3609, h3646, hlam]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          rcases p3625_3 (m.d 0 3) (by simp) with h3649 | h3649
                          · linarith only [h2760, h3649, hlam]
                          · linarith only [h3610, h3649, hlam]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3607, hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3612, hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h0, h3607, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3625_1, u4ehi3]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h0, h3607, h3623, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3625_1, u4ehi3]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3609, hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3614, hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3617, hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3623, hlam, p3625_1]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3610, hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3615, hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3618, hlam, p3625_0]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [h3610, hc03, hlam, hphi, ht0b, ht45, ht5b, p3625_1, u4ehi3]
                        · have p3625_0 := h3625c.1
                          have p3625_1 := h3625c.2.1
                          have p3625_2 := h3625c.2.2.1
                          have p3625_3 := h3625c.2.2.2
                          linarith only [hlam, p3625_0]
                  · linarith only [h2760, h3610, h3612, h3617, h3618, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3668 | h3668
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3669 | h3669
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3670 | h3670
                      · linarith only [h2760, h3609, h3612, h3617, h3668, h3670, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h3617, h3668, h3669, h3670, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h3617, h3668, h3669, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3674 | h3674
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3675 | h3675
                      · rcases h3bigk with h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h2760, hlam, p3676_1]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          rcases p3676_3 (m.d 0 3) (by simp) with h3679 | h3679
                          · rcases p3676_3 (m.d 1 3) (by simp) with h3680 | h3680
                            · rcases p3676_3 (m.d 2 3) (by simp) with h3681 | h3681
                              · linarith only [h3607, h3681, hlam]
                              · rcases p3676_3 (m.d 3 4) (by simp) with h3683 | h3683
                                · linarith only [h3609, h3683, hlam]
                                · linarith only [h3617, h3683, hlam]
                            · linarith only [h3612, h3680, hlam]
                          · linarith only [h3607, h3679, hlam]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h2760, h3612, h3617, h3674, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3676_1, u4ehi4]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          rcases p3676_3 (m.d 0 3) (by simp) with h3689 | h3689
                          · rcases p3676_3 (m.d 1 3) (by simp) with h3690 | h3690
                            · rcases p3676_3 (m.d 2 3) (by simp) with h3691 | h3691
                              · linarith only [h3607, h3691, hlam]
                              · rcases p3676_3 (m.d 3 4) (by simp) with h3693 | h3693
                                · linarith only [h3609, h3693, hlam]
                                · linarith only [h3675, h3693, hlam]
                            · linarith only [h3615, h3690, hlam]
                          · linarith only [h3689, hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3609, h3612, h3617, h3674, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3676_1, u4ehi4]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          rcases p3676_3 (m.d 0 3) (by simp) with h3700 | h3700
                          · linarith only [h2760, h3700, hlam]
                          · linarith only [h3607, h3700, hlam]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3612, h3617, h3674, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3676_1, u4ehi4]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          rcases p3676_3 (m.d 0 3) (by simp) with h3704 | h3704
                          · linarith only [h2760, h3704, hlam]
                          · linarith only [h3610, h3704, hlam]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3607, hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3612, hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3617, hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3668, hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3609, hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3614, hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          rcases p3676_3 (m.d 0 3) (by simp) with h3714 | h3714
                          · rcases p3676_3 (m.d 1 3) (by simp) with h3715 | h3715
                            · rcases p3676_3 (m.d 2 3) (by simp) with h3716 | h3716
                              · linarith only [h3716, hlam, p3676_0]
                              · rcases p3676_3 (m.d 3 4) (by simp) with h3718 | h3718
                                · rcases p3676_3 (m.d 3 5) (by simp) with h3719 | h3719
                                  · linarith only [h3675, h3719, hlam]
                                  · linarith only [h3668, h3719, hlam]
                                · linarith only [h3718, hlam, p3676_0]
                            · linarith only [h3612, h3715, hlam]
                          · linarith only [h3607, h3714, hlam]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3668, hc23, hc34, hlam, hphi, p3676_1]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3610, hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3615, hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          rcases p3676_3 (m.d 0 3) (by simp) with h3729 | h3729
                          · rcases p3676_3 (m.d 1 3) (by simp) with h3730 | h3730
                            · rcases p3676_3 (m.d 2 3) (by simp) with h3731 | h3731
                              · linarith only [h3731, hlam, p3676_0]
                              · rcases p3676_3 (m.d 3 4) (by simp) with h3733 | h3733
                                · rcases p3676_3 (m.d 3 5) (by simp) with h3734 | h3734
                                  · rcases h4bigk with h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c | h3735c
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3404, hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3609, h3674, hc03, hlam, hphi, ht0b, ht45, ht5b, p3735_1, u4ehi4]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h2760, h3609, h3612, h3617, h3674, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3735_1, u4ehi4]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      rcases p3735_3 (m.d 0 4) (by simp) with h3740 | h3740
                                      · rcases p3735_3 (m.d 1 4) (by simp) with h3741 | h3741
                                        · rcases p3735_3 (m.d 2 4) (by simp) with h3742 | h3742
                                          · linarith only [h3608, h3742, hlam]
                                          · linarith only [h3674, h3742, hlam]
                                        · linarith only [h3616, h3741, hlam]
                                      · linarith only [h3740, hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3608, h3612, h3614, h3674, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3735_1, u4ehi4]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3612, h3614, h3674, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3735_1, u4ehi4]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3612, h3614, h3675, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3676_1, p3735_1]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      rcases p3735_3 (m.d 0 4) (by simp) with h3751 | h3751
                                      · linarith only [h3404, h3751, hlam]
                                      · linarith only [h3611, h3751, hlam]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3608, hlam, p3735_1]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3613, hlam, p3735_1]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3617, hlam, p3735_1]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h0, h3608, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3735_1, u4ehi4]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3609, hlam, p3735_1]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3614, hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h2760, h3609, h3612, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3735_1, u4ehi2]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h2760, h3609, h3612, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3735_1, u4ehi4]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3611, hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3616, hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3674, hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [h3675, hlam, p3735_0]
                                    · have p3735_0 := h3735c.1
                                      have p3735_1 := h3735c.2.1
                                      have p3735_2 := h3735c.2.2.1
                                      have p3735_3 := h3735c.2.2.2
                                      linarith only [hlam, p3735_0]
                                  · linarith only [h3734, hlam, p3676_0]
                                · linarith only [h3617, h3733, hlam]
                            · linarith only [h3612, h3730, hlam]
                          · linarith only [h3607, h3729, hlam]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [h3675, hlam, p3676_0]
                        · have p3676_0 := h3676c.1
                          have p3676_1 := h3676c.2.1
                          have p3676_2 := h3676c.2.2.1
                          have p3676_3 := h3676c.2.2.2
                          linarith only [hlam, p3676_0]
                      · linarith only [h0, h3608, h3674, h3675, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3776 | h3776
                      · linarith only [h2760, h3609, h3612, h3674, h3776, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases h3bigk with h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h2760, hlam, p3778_1]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3609, h3611, h3617, h3776, hlam, p3778_2]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          rcases p3778_3 (m.d 0 3) (by simp) with h3782 | h3782
                          · rcases p3778_3 (m.d 1 3) (by simp) with h3783 | h3783
                            · rcases p3778_3 (m.d 2 3) (by simp) with h3784 | h3784
                              · linarith only [h3607, h3784, hlam]
                              · rcases p3778_3 (m.d 3 4) (by simp) with h3786 | h3786
                                · linarith only [h3786, hlam, p3778_0]
                                · rcases p3778_3 (m.d 3 5) (by simp) with h3788 | h3788
                                  · linarith only [h3610, h3788, hlam]
                                  · linarith only [h3776, h3788, hlam]
                            · linarith only [h3614, h3783, hlam]
                          · linarith only [h3782, hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          rcases p3778_3 (m.d 0 3) (by simp) with h3793 | h3793
                          · rcases p3778_3 (m.d 1 3) (by simp) with h3794 | h3794
                            · rcases p3778_3 (m.d 2 3) (by simp) with h3795 | h3795
                              · linarith only [h3607, h3795, hlam]
                              · rcases p3778_3 (m.d 3 4) (by simp) with h3797 | h3797
                                · linarith only [h3609, h3797, hlam]
                                · rcases p3778_3 (m.d 3 5) (by simp) with h3799 | h3799
                                  · linarith only [h3799, hlam, p3778_0]
                                  · rcases h4bigk with h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [hlam, p3801_0]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3404, hlam, p3801_0]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      rcases p3801_3 (m.d 0 4) (by simp) with h3804 | h3804
                                      · rcases p3801_3 (m.d 1 4) (by simp) with h3805 | h3805
                                        · rcases p3801_3 (m.d 2 4) (by simp) with h3806 | h3806
                                          · linarith only [h3608, h3806, hlam]
                                          · rcases p3801_3 (m.d 3 4) (by simp) with h3808 | h3808
                                            · linarith only [h3609, h3808, hlam]
                                            · linarith only [h3617, h3808, hlam]
                                        · linarith only [h3613, h3805, hlam]
                                      · linarith only [h3608, h3804, hlam]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      rcases p3801_3 (m.d 0 4) (by simp) with h3813 | h3813
                                      · rcases p3801_3 (m.d 1 4) (by simp) with h3814 | h3814
                                        · rcases p3801_3 (m.d 2 4) (by simp) with h3815 | h3815
                                          · linarith only [h3608, h3815, hlam]
                                          · rcases p3801_3 (m.d 3 4) (by simp) with h3817 | h3817
                                            · linarith only [h3609, h3817, hlam]
                                            · rcases p3801_3 (m.d 4 5) (by simp) with h3819 | h3819
                                              · linarith only [h3611, h3819, hlam]
                                              · linarith only [h3776, h3819, hlam]
                                        · linarith only [h3614, h3814, hlam]
                                      · linarith only [h3609, h3813, hlam]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3617, h3776, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3801_1]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3611, h3612, h3614, h3617, h3776, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3801_1]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [hlam, p3801_0]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      rcases p3801_3 (m.d 0 4) (by simp) with h3827 | h3827
                                      · linarith only [h3404, h3827, hlam]
                                      · linarith only [h3608, h3827, hlam]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      rcases p3801_3 (m.d 0 4) (by simp) with h3830 | h3830
                                      · linarith only [h3404, h3830, hlam]
                                      · linarith only [h3609, h3830, hlam]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3612, h3614, h3617, h3776, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3801_1]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3608, hlam, p3801_1]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3613, hlam, p3801_1]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [hlam, p3801_0]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3617, hlam, p3801_1]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3674, hlam, p3801_0]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3609, hlam, p3801_1]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3614, hlam, p3801_0]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3611, h3776, hc04, hlam, hphi, ht0b, ht45, ht5b, p3801_1, u4ehi2]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [hlam, p3801_0]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3776, hlam, p3801_0]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3611, hlam, p3801_0]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3616, hlam, p3801_0]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3404, h3611, h3612, h3614, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3801_1, u4ehi2]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [h3404, h3611, h3612, h3614, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3801_1, u4ehi3]
                                    · have p3801_0 := h3801c.1
                                      have p3801_1 := h3801c.2.1
                                      have p3801_2 := h3801c.2.2.1
                                      have p3801_3 := h3801c.2.2.2
                                      linarith only [hlam, p3801_0]
                            · linarith only [h3615, h3794, hlam]
                          · linarith only [h3793, hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3609, h3612, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3778_1, u4ehi3]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3404, h3611, h3614, h3617, h3776, hlam, p3778_2]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          rcases p3778_3 (m.d 0 3) (by simp) with h3854 | h3854
                          · linarith only [h2760, h3854, hlam]
                          · linarith only [h3609, h3854, hlam]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          rcases p3778_3 (m.d 0 3) (by simp) with h3857 | h3857
                          · linarith only [h2760, h3857, hlam]
                          · linarith only [h3610, h3857, hlam]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3607, hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3612, hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3617, hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3668, hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3609, hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3614, hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3404, h3611, h3612, h3614, h3776, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3778_1]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3776, hlam, p3778_1]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3610, hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3615, hlam, p3778_0]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          rcases p3778_3 (m.d 0 3) (by simp) with h3872 | h3872
                          · rcases p3778_3 (m.d 1 3) (by simp) with h3873 | h3873
                            · rcases p3778_3 (m.d 2 3) (by simp) with h3874 | h3874
                              · linarith only [h3874, hlam, p3778_0]
                              · rcases p3778_3 (m.d 3 4) (by simp) with h3876 | h3876
                                · linarith only [h3776, h3876, hlam]
                                · linarith only [h3617, h3876, hlam]
                            · linarith only [h3612, h3873, hlam]
                          · linarith only [h3607, h3872, hlam]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [h3610, hc03, hlam, hphi, ht0b, ht45, ht5b, p3778_1, u4ehi3]
                        · have p3778_0 := h3778c.1
                          have p3778_1 := h3778c.2.1
                          have p3778_2 := h3778c.2.2.1
                          have p3778_3 := h3778c.2.2.2
                          linarith only [hlam, p3778_0]
              · linarith only [h3404, h3611, h3616, hlam]
            · linarith only [h2760, h3610, h3615, hlam]
          · linarith only [h2760, h3609, h3614, hlam]
        · linarith only [h0, h3608, h3613, hlam]
      · linarith only [h0, h3607, h3612, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3888 | h3888
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3889 | h3889
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3890 | h3890
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3891 | h3891
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3892 | h3892
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3893 | h3893
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3894 | h3894
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3895 | h3895
                    · linarith only [h3608, h3611, h3895, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3897 | h3897
                      · linarith only [h3608, h3611, h3893, h3897, hlam]
                      · rcases h3bigk with h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c | h3899c
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h2760, hlam, p3899_1]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3607, h3893, hc02, hlam, hphi, ht0b, ht45, ht5b, p3899_1, u4ehi3]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          rcases p3899_3 (m.d 0 3) (by simp) with h3903 | h3903
                          · rcases p3899_3 (m.d 1 3) (by simp) with h3904 | h3904
                            · rcases p3899_3 (m.d 2 3) (by simp) with h3905 | h3905
                              · linarith only [h3607, h3905, hlam]
                              · linarith only [h3893, h3905, hlam]
                            · linarith only [h3890, h3904, hlam]
                          · linarith only [h3903, hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          rcases p3899_3 (m.d 0 3) (by simp) with h3910 | h3910
                          · rcases p3899_3 (m.d 1 3) (by simp) with h3911 | h3911
                            · rcases p3899_3 (m.d 2 3) (by simp) with h3912 | h3912
                              · linarith only [h3607, h3912, hlam]
                              · linarith only [h3894, h3912, hlam]
                            · linarith only [h3891, h3911, hlam]
                          · linarith only [h3910, hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3607, h3894, h3897, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p3899_1, u4ehi3]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3888, h3894, h3897, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3899_1, u4ehi3]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          rcases p3899_3 (m.d 0 3) (by simp) with h3920 | h3920
                          · linarith only [h2760, h3920, hlam]
                          · linarith only [h3609, h3920, hlam]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          rcases p3899_3 (m.d 0 3) (by simp) with h3923 | h3923
                          · linarith only [h2760, h3923, hlam]
                          · linarith only [h3610, h3923, hlam]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3607, hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3888, hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h0, h3607, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3899_1, u4ehi3]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h0, h3607, h3897, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3899_1, u4ehi3]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3609, hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3890, hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3893, hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3897, hlam, p3899_1]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3610, hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3891, hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3894, hlam, p3899_0]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [h3610, hc03, hlam, hphi, ht0b, ht45, ht5b, p3899_1, u4ehi3]
                        · have p3899_0 := h3899c.1
                          have p3899_1 := h3899c.2.1
                          have p3899_2 := h3899c.2.2.1
                          have p3899_3 := h3899c.2.2.2
                          linarith only [hlam, p3899_0]
                  · linarith only [h3610, h3893, h3894, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3942 | h3942
                  · linarith only [h3609, h3611, h3888, h3890, h3892, h3893, h3942, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3944 | h3944
                    · linarith only [h3609, h3611, h3893, h3944, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3946 | h3946
                      · linarith only [h3609, h3611, h3946, hlam]
                      · rcases h3bigk with h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c | h3948c
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h2760, hlam, p3948_1]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          rcases p3948_3 (m.d 0 3) (by simp) with h3951 | h3951
                          · rcases p3948_3 (m.d 1 3) (by simp) with h3952 | h3952
                            · rcases p3948_3 (m.d 2 3) (by simp) with h3953 | h3953
                              · linarith only [h3607, h3953, hlam]
                              · rcases p3948_3 (m.d 3 4) (by simp) with h3955 | h3955
                                · linarith only [h3609, h3955, hlam]
                                · linarith only [h3893, h3955, hlam]
                            · linarith only [h3888, h3952, hlam]
                          · linarith only [h3607, h3951, hlam]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          rcases p3948_3 (m.d 0 3) (by simp) with h3960 | h3960
                          · rcases p3948_3 (m.d 1 3) (by simp) with h3961 | h3961
                            · rcases p3948_3 (m.d 2 3) (by simp) with h3962 | h3962
                              · linarith only [h3607, h3962, hlam]
                              · rcases p3948_3 (m.d 3 4) (by simp) with h3964 | h3964
                                · linarith only [h3964, hlam, p3948_0]
                                · rcases p3948_3 (m.d 3 5) (by simp) with h3966 | h3966
                                  · linarith only [h3610, h3966, hlam]
                                  · linarith only [h3946, h3966, hlam]
                            · linarith only [h3890, h3961, hlam]
                          · linarith only [h3960, hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          rcases p3948_3 (m.d 0 3) (by simp) with h3971 | h3971
                          · rcases p3948_3 (m.d 1 3) (by simp) with h3972 | h3972
                            · rcases p3948_3 (m.d 2 3) (by simp) with h3973 | h3973
                              · linarith only [h3607, h3973, hlam]
                              · rcases p3948_3 (m.d 3 4) (by simp) with h3975 | h3975
                                · linarith only [h3609, h3975, hlam]
                                · rcases p3948_3 (m.d 3 5) (by simp) with h3977 | h3977
                                  · linarith only [h3977, hlam, p3948_0]
                                  · rcases h4bigk with h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c | h3979c
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [hlam, p3979_0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3404, hlam, p3979_0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3611, h3888, h3890, h3892, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3979_1, u4ehi2]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3611, h3888, h3890, h3892, h3893, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3979_1]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3611, hlam, p3979_0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      rcases p3979_3 (m.d 0 4) (by simp) with h3985 | h3985
                                      · linarith only [h3404, h3985, hlam]
                                      · rcases p3979_3 (m.d 1 4) (by simp) with h3987 | h3987
                                        · rcases p3979_3 (m.d 2 4) (by simp) with h3988 | h3988
                                          · linarith only [h3889, h3988, hlam]
                                          · rcases p3979_3 (m.d 3 4) (by simp) with h3990 | h3990
                                            · linarith only [h3890, h3990, hlam]
                                            · rcases p3979_3 (m.d 4 5) (by simp) with h3992 | h3992
                                              · linarith only [h3892, h3992, hlam]
                                              · linarith only [h3611, h3992, hlam]
                                        · linarith only [h3404, h3987, hlam]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [hlam, p3979_0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      rcases p3979_3 (m.d 0 4) (by simp) with h3997 | h3997
                                      · linarith only [h3404, h3997, hlam]
                                      · linarith only [h3608, h3997, hlam]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      rcases p3979_3 (m.d 0 4) (by simp) with h4000 | h4000
                                      · linarith only [h3404, h4000, hlam]
                                      · linarith only [h3609, h4000, hlam]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3611, h3888, h3890, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3979_1, u4ehi0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3608, hlam, p3979_1]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3889, hlam, p3979_1]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [hlam, p3979_0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3893, hlam, p3979_1]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3944, hlam, p3979_0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3609, hlam, p3979_1]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3890, hlam, p3979_0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3609, h3611, hc45, hlam, hphi, p3979_1, u4ehi2]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [hlam, p3979_0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3946, hlam, p3979_0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [hc45, hlam, hphi, p3979_1, u4ehi0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3892, hlam, p3979_0]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3888, h3890, h3892, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3979_1, u4ehi2]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [h3888, h3890, h3892, h3893, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3979_1]
                                    · have p3979_0 := h3979c.1
                                      have p3979_1 := h3979c.2.1
                                      have p3979_2 := h3979c.2.2.1
                                      have p3979_3 := h3979c.2.2.2
                                      linarith only [hlam, p3979_0]
                            · linarith only [h3891, h3972, hlam]
                          · linarith only [h3971, hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3609, h3888, h3893, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3948_1]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3609, h3611, h3890, h3892, h3893, hlam, p3948_2]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          rcases p3948_3 (m.d 0 3) (by simp) with h4024 | h4024
                          · linarith only [h2760, h4024, hlam]
                          · linarith only [h3609, h4024, hlam]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          rcases p3948_3 (m.d 0 3) (by simp) with h4027 | h4027
                          · linarith only [h2760, h4027, hlam]
                          · linarith only [h3610, h4027, hlam]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3607, hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3888, hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3893, hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3942, hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3609, hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3890, hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3609, h3611, h3888, h3890, h3892, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3948_1]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3946, hlam, p3948_1]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3610, hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3891, hlam, p3948_0]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          rcases p3948_3 (m.d 0 3) (by simp) with h4042 | h4042
                          · rcases p3948_3 (m.d 1 3) (by simp) with h4043 | h4043
                            · rcases p3948_3 (m.d 2 3) (by simp) with h4044 | h4044
                              · linarith only [h4044, hlam, p3948_0]
                              · rcases p3948_3 (m.d 3 4) (by simp) with h4046 | h4046
                                · linarith only [h3946, h4046, hlam]
                                · linarith only [h3893, h4046, hlam]
                            · linarith only [h3888, h4043, hlam]
                          · linarith only [h3607, h4042, hlam]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [h3610, hc03, hlam, hphi, ht0b, ht45, ht5b, p3948_1, u4ehi3]
                        · have p3948_0 := h3948c.1
                          have p3948_1 := h3948c.2.1
                          have p3948_2 := h3948c.2.2.1
                          have p3948_3 := h3948c.2.2.2
                          linarith only [hlam, p3948_0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4053 | h4053
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4054 | h4054
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4055 | h4055
                    · linarith only [h3404, h3892, h4055, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4057 | h4057
                      · linarith only [h3404, h3892, h4053, h4057, hc01, hc23, hlam, hphi, ht12]
                      · rcases h3bigk with h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h2760, hlam, p4059_1]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h2760, h3888, h4053, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4059_1, u4ehi3]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          rcases p4059_3 (m.d 0 3) (by simp) with h4063 | h4063
                          · rcases p4059_3 (m.d 1 3) (by simp) with h4064 | h4064
                            · rcases p4059_3 (m.d 2 3) (by simp) with h4065 | h4065
                              · linarith only [h3607, h4065, hlam]
                              · linarith only [h4053, h4065, hlam]
                            · linarith only [h3890, h4064, hlam]
                          · linarith only [h4063, hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          rcases p4059_3 (m.d 0 3) (by simp) with h4070 | h4070
                          · rcases p4059_3 (m.d 1 3) (by simp) with h4071 | h4071
                            · rcases p4059_3 (m.d 2 3) (by simp) with h4072 | h4072
                              · linarith only [h3607, h4072, hlam]
                              · linarith only [h4054, h4072, hlam]
                            · linarith only [h3891, h4071, hlam]
                          · linarith only [h4070, hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h3607, h3888, h4054, h4057, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4059_1, u4ehi3]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h3888, h4054, h4057, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4059_1, u4ehi3]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          rcases p4059_3 (m.d 0 3) (by simp) with h4080 | h4080
                          · linarith only [h2760, h4080, hlam]
                          · linarith only [h3609, h4080, hlam]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          rcases p4059_3 (m.d 0 3) (by simp) with h4083 | h4083
                          · linarith only [h2760, h4083, hlam]
                          · linarith only [h3610, h4083, hlam]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h3607, hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h3888, hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h0, h3607, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4059_1, u4ehi3]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h0, h3607, h4057, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4059_1, u4ehi3]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h3609, hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h3890, hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h4053, hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h4057, hlam, p4059_1]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h3610, hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h3891, hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h4054, hlam, p4059_0]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [h3610, hc03, hlam, hphi, ht0b, ht45, ht5b, p4059_1, u4ehi3]
                        · have p4059_0 := h4059c.1
                          have p4059_1 := h4059c.2.1
                          have p4059_2 := h4059c.2.2.1
                          have p4059_3 := h4059c.2.2.2
                          linarith only [hlam, p4059_0]
                  · linarith only [h2760, h3610, h3888, h4053, h4054, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4102 | h4102
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4103 | h4103
                    · linarith only [h3404, h3609, h3892, h4053, h4103, hlam]
                    · linarith only [h3404, h3609, h3892, h4053, h4102, h4103, hc45, hlam, hphi, u4ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4106 | h4106
                    · linarith only [h3404, h3892, h4106, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4108 | h4108
                      · linarith only [h3404, h3609, h3892, h4108, hlam]
                      · rcases h3bigk with h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h2760, hlam, p4110_1]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          rcases p4110_3 (m.d 0 3) (by simp) with h4113 | h4113
                          · rcases p4110_3 (m.d 1 3) (by simp) with h4114 | h4114
                            · rcases p4110_3 (m.d 2 3) (by simp) with h4115 | h4115
                              · linarith only [h3607, h4115, hlam]
                              · rcases p4110_3 (m.d 3 4) (by simp) with h4117 | h4117
                                · linarith only [h3609, h4117, hlam]
                                · linarith only [h4053, h4117, hlam]
                            · linarith only [h3888, h4114, hlam]
                          · linarith only [h3607, h4113, hlam]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          rcases p4110_3 (m.d 0 3) (by simp) with h4122 | h4122
                          · rcases p4110_3 (m.d 1 3) (by simp) with h4123 | h4123
                            · rcases p4110_3 (m.d 2 3) (by simp) with h4124 | h4124
                              · linarith only [h3607, h4124, hlam]
                              · rcases p4110_3 (m.d 3 4) (by simp) with h4126 | h4126
                                · linarith only [h4126, hlam, p4110_0]
                                · rcases p4110_3 (m.d 3 5) (by simp) with h4128 | h4128
                                  · linarith only [h3610, h4128, hlam]
                                  · linarith only [h4108, h4128, hlam]
                            · linarith only [h3890, h4123, hlam]
                          · linarith only [h4122, hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          rcases p4110_3 (m.d 0 3) (by simp) with h4133 | h4133
                          · rcases p4110_3 (m.d 1 3) (by simp) with h4134 | h4134
                            · rcases p4110_3 (m.d 2 3) (by simp) with h4135 | h4135
                              · linarith only [h3607, h4135, hlam]
                              · rcases p4110_3 (m.d 3 4) (by simp) with h4137 | h4137
                                · linarith only [h3609, h4137, hlam]
                                · rcases p4110_3 (m.d 3 5) (by simp) with h4139 | h4139
                                  · linarith only [h4139, hlam, p4110_0]
                                  · rcases h4bigk with h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c | h4141c
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [hlam, p4141_0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3404, hlam, p4141_0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3404, h3892, hc45, hlam, hphi, p4141_1, u4ehi2]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3404, h3892, hc45, hlam, hphi, p4141_1, u4ehi3]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3611, hlam, p4141_0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3892, hc45, hlam, hphi, p4141_1, u4ehi0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [hlam, p4141_0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3892, hc45, hlam, hphi, p4141_1, u4ehi2]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3892, hc45, hlam, hphi, p4141_1, u4ehi3]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3892, hlam, p4141_0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3608, hlam, p4141_1]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3889, hlam, p4141_1]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [hlam, p4141_0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h4053, hlam, p4141_1]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h4106, hlam, p4141_0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3609, hlam, p4141_1]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3890, hlam, p4141_0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h3404, h3609, h3892, hc45, hlam, hphi, p4141_1, u4ehi2]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [hlam, p4141_0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h4108, hlam, p4141_0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [hc45, hlam, hphi, p4141_1, u4ehi0]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [hc45, hlam, hphi, p4141_1, u4ehi1]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [hc45, hlam, hphi, p4141_1, u4ehi2]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [h4053, hc23, hc45, hlam, hphi, ht34, p4141_1]
                                    · have p4141_0 := h4141c.1
                                      have p4141_1 := h4141c.2.1
                                      have p4141_2 := h4141c.2.2.1
                                      have p4141_3 := h4141c.2.2.2
                                      linarith only [hlam, p4141_0]
                            · linarith only [h3891, h4134, hlam]
                          · linarith only [h4133, hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h3609, h3888, h4053, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4110_1]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          rcases p4110_3 (m.d 0 3) (by simp) with h4171 | h4171
                          · linarith only [h2760, h4171, hlam]
                          · linarith only [h3607, h4171, hlam]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          rcases p4110_3 (m.d 0 3) (by simp) with h4174 | h4174
                          · linarith only [h2760, h4174, hlam]
                          · linarith only [h3609, h4174, hlam]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          rcases p4110_3 (m.d 0 3) (by simp) with h4177 | h4177
                          · linarith only [h2760, h4177, hlam]
                          · linarith only [h3610, h4177, hlam]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h3607, hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h3888, hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h4053, hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h4102, hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h3609, hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h3890, hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h3609, h3611, hc23, hc45, hlam, hphi, ht34, p4110_1]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h4108, hlam, p4110_1]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h3610, hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h3891, hlam, p4110_0]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          rcases p4110_3 (m.d 0 3) (by simp) with h4192 | h4192
                          · rcases p4110_3 (m.d 1 3) (by simp) with h4193 | h4193
                            · rcases p4110_3 (m.d 2 3) (by simp) with h4194 | h4194
                              · linarith only [h4194, hlam, p4110_0]
                              · rcases p4110_3 (m.d 3 4) (by simp) with h4196 | h4196
                                · linarith only [h4108, h4196, hlam]
                                · linarith only [h4053, h4196, hlam]
                            · linarith only [h3888, h4193, hlam]
                          · linarith only [h3607, h4192, hlam]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [h3610, hc03, hlam, hphi, ht0b, ht45, ht5b, p4110_1, u4ehi3]
                        · have p4110_0 := h4110c.1
                          have p4110_1 := h4110c.2.1
                          have p4110_2 := h4110c.2.2.1
                          have p4110_3 := h4110c.2.2.2
                          linarith only [hlam, p4110_0]
            · linarith only [h2760, h3610, h3891, hlam]
          · linarith only [h2760, h3609, h3890, hlam]
        · linarith only [h0, h3608, h3889, hlam]
      · linarith only [h0, h3607, h3888, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4207 | h4207
    · linarith only [h3609, h3610, h4207, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4209 | h4209
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4210 | h4210
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4211 | h4211
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4212 | h4212
            · linarith only [h3609, h3610, h4212, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4214 | h4214
              · linarith only [h4207, h4211, h4212, h4214, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4216 | h4216
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4217 | h4217
                  · linarith only [h2760, h3607, h4212, h4217, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4219 | h4219
                    · linarith only [h3404, h4214, h4219, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4221 | h4221
                      · linarith only [h2760, h3404, h3607, h4212, h4214, h4216, h4221, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h2760, h3607, h4212, h4216, h4221, hc45, hlam, hphi, u4ehi3]
                · linarith only [h2760, h3609, h4212, h4216, hc23, hc35, hlam, hphi]
          · linarith only [h2760, h3609, h4211, hlam]
        · linarith only [h0, h3608, h4210, hlam]
      · linarith only [h0, h3607, h4209, hlam]

end R2N4
