import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2837 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3271 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3539 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3540 | h3540
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3541 | h3541
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3542 | h3542
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3543 | h3543
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3544 | h3544
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3545 | h3545
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3546 | h3546
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3547 | h3547
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3548 | h3548
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3549 | h3549
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3550 | h3550
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3551 | h3551
                        · linarith only [h3543, h3549, h3551, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h3271, h3539, h3545, h3546, h3550, h3551, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h3271, h3539, h3543, h3546, h3548, h3550, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3555 | h3555
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3556 | h3556
                        · rcases h1bigk with h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h0, hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h2837, hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3271, hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3271, h3543, h3546, hc15, hlam, hphi, ht01, ht0b, ht5b, p3557_1, u1elo1]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [hc01, hlam, hphi, p3557_1, u1elo1]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h2837, hc01, hlam, hphi, p3557_1, u1elo1]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3271, h3539, h3547, hc35, hlam, hphi, ht01, ht0b, ht5b, p3557_1, u1elo1]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            rcases p3557_3 (m.d 0 1) (by simp) with h3567 | h3567
                            · linarith only [h0, h3567, hlam]
                            · linarith only [h3539, h3567, hlam]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3539, h3545, h3555, hc45, hlam, hphi, ht01, ht0b, ht5b, p3557_1, u1elo2]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3543, hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3271, h3539, h3543, h3545, h3555, hc45, hlam, hphi, ht01, ht0b, ht5b, p3557_1, u1elo1]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            rcases p3557_3 (m.d 0 1) (by simp) with h3574 | h3574
                            · linarith only [h2837, h3574, hlam]
                            · linarith only [h3539, h3574, hlam]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3539, h3545, h3555, hc45, hlam, hphi, ht01, ht0b, ht5b, p3557_1, u1elo3]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3544, hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3546, hlam, p3557_1]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            rcases p3557_3 (m.d 0 1) (by simp) with h3581 | h3581
                            · linarith only [h3271, h3581, hlam]
                            · linarith only [h3539, h3581, hlam]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3539, hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3545, hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3547, hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [h3548, hlam, p3557_0]
                          · have p3557_0 := h3557c.1
                            have p3557_1 := h3557c.2.1
                            have p3557_2 := h3557c.2.2.1
                            have p3557_3 := h3557c.2.2.2
                            linarith only [hlam, p3557_0]
                        · linarith only [h3539, h3545, h3549, h3555, h3556, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h3271, h3539, h3543, h3546, h3548, h3555, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h2837, h3271, h3541, h3542, h3543, h3548, hc01, hlam, hphi, u1elo1]
                · linarith only [h3271, h3539, h3546, h3547, hlam]
              · linarith only [h2837, h3541, h3546, hlam]
            · linarith only [h2837, h3271, h3539, h3541, h3543, h3545, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
          · linarith only [h0, h3540, h3544, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3596 | h3596
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3597 | h3597
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3598 | h3598
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3599 | h3599
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3600 | h3600
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3601 | h3601
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3602 | h3602
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3603 | h3603
                        · rcases h1bigk with h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c | h3604c
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h0, hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h2837, hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3271, hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h0, h3543, h3597, h3602, hc45, hlam, hphi, ht01, ht0b, ht5b, p3604_1, u1elo2]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3543, hc01, hlam, hphi, p3604_1, u1elo2]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3543, hlam, p3604_1]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3271, h3543, hc01, hlam, hphi, p3604_1, u1elo2]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            rcases p3604_3 (m.d 0 1) (by simp) with h3614 | h3614
                            · linarith only [h0, h3614, hlam]
                            · linarith only [h3539, h3614, hlam]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3539, h3597, h3602, hc45, hlam, hphi, ht01, ht0b, ht5b, p3604_1, u1elo2]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h0, h3540, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3604_1, u1elo2]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3271, h3539, h3597, h3602, hc45, hlam, hphi, ht01, ht0b, ht5b, p3604_1, u1elo2]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            rcases p3604_3 (m.d 0 1) (by simp) with h3621 | h3621
                            · linarith only [h2837, h3621, hlam]
                            · linarith only [h3539, h3621, hlam]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3539, h3596, h3597, h3602, hc45, hlam, hphi, ht01, ht0b, ht5b, p3604_1, u1elo1]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3596, hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3598, hlam, p3604_1]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            rcases p3604_3 (m.d 0 1) (by simp) with h3628 | h3628
                            · linarith only [h3271, h3628, hlam]
                            · linarith only [h3539, h3628, hlam]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3539, hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3597, hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3599, hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [h3600, hlam, p3604_0]
                          · have p3604_0 := h3604c.1
                            have p3604_1 := h3604c.2.1
                            have p3604_2 := h3604c.2.2.1
                            have p3604_3 := h3604c.2.2.2
                            linarith only [hlam, p3604_0]
                        · linarith only [h0, h3539, h3543, h3597, h3602, h3603, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h3271, h3539, h3543, h3596, h3600, h3601, h3602, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h3271, h3543, h3596, h3601, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3271, h3539, h3540, h3542, h3597, h3600, hc02, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h3539, h3543, h3599, hlam]
              · linarith only [h2837, h3541, h3598, hlam]
            · linarith only [h3271, h3539, h3596, h3597, hlam]
          · linarith only [h0, h3540, h3596, hlam]
      · linarith only [h3271, h3539, h3542, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3645 | h3645
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3646 | h3646
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3647 | h3647
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3648 | h3648
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3649 | h3649
              · linarith only [h2837, h3541, h3646, h3649, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3651 | h3651
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3652 | h3652
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3653 | h3653
                    · linarith only [h2837, h3539, h3646, h3648, h3649, h3653, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3655 | h3655
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3656 | h3656
                        · rcases h1bigk with h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c | h3657c
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h0, hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h2837, hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3271, hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h2837, h3648, h3655, hc45, hlam, hphi, ht01, ht0b, ht5b, p3657_1, u1elo2]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [hc01, hlam, hphi, p3657_1, u1elo1]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h2837, h3539, h3648, h3655, hc45, hlam, hphi, ht01, ht0b, ht5b, p3657_1, u1elo1]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3271, h3539, h3648, h3655, hc45, hlam, hphi, ht01, ht0b, ht5b, p3657_1, u1elo1]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            rcases p3657_3 (m.d 0 1) (by simp) with h3667 | h3667
                            · linarith only [h0, h3667, hlam]
                            · linarith only [h3539, h3667, hlam]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3539, h3648, h3655, hc45, hlam, hphi, ht01, ht0b, ht5b, p3657_1, u1elo2]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3646, hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3649, hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            rcases p3657_3 (m.d 0 1) (by simp) with h3674 | h3674
                            · linarith only [h2837, h3674, hlam]
                            · linarith only [h3539, h3674, hlam]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3539, h3647, h3648, h3655, hc45, hlam, hphi, ht01, ht0b, ht5b, p3657_1, u1elo1]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3647, hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h2837, h3539, h3647, h3648, h3655, hc45, hlam, hphi, ht01, ht0b, ht5b, p3657_1, u1elo1]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            rcases p3657_3 (m.d 0 1) (by simp) with h3681 | h3681
                            · linarith only [h3271, h3681, hlam]
                            · linarith only [h3539, h3681, hlam]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3539, hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3648, hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3651, hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [h3652, hlam, p3657_0]
                          · have p3657_0 := h3657c.1
                            have p3657_1 := h3657c.2.1
                            have p3657_2 := h3657c.2.2.1
                            have p3657_3 := h3657c.2.2.2
                            linarith only [hlam, p3657_0]
                        · linarith only [h2837, h3539, h3648, h3655, h3656, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h2837, h3539, h3645, h3649, h3653, h3655, hc23, hc34, hlam, hphi]
                  · linarith only [h3271, h3539, h3645, h3652, hlam]
                · linarith only [h2837, h3539, h3651, hlam]
            · linarith only [h0, h3539, h3648, hlam]
          · linarith only [h2837, h3539, h3540, h3646, h3647, hc02, hc15, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3695 | h3695
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3696 | h3696
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3697 | h3697
              · linarith only [h2837, h3539, h3541, h3696, h3697, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · linarith only [h3646, h3695, h3697, hlam]
            · linarith only [h0, h3539, h3696, hlam]
          · linarith only [h0, h3540, h3695, hlam]
      · linarith only [h2837, h3539, h3541, h3645, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3703 | h3703
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3704 | h3704
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3705 | h3705
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3706 | h3706
          · linarith only [h0, h3540, h3706, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3708 | h3708
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3709 | h3709
              · linarith only [h3705, h3706, h3709, hlam]
              · linarith only [h2837, h3703, h3709, hlam]
            · linarith only [h0, h3539, h3708, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3713 | h3713
          · linarith only [h0, h3540, h3705, h3713, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3715 | h3715
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3716 | h3716
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3717 | h3717
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3718 | h3718
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3719 | h3719
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3720 | h3720
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3721 | h3721
                        · rcases h1bigk with h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c | h3722c
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h0, hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h2837, hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3271, hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h0, h3713, h3715, h3716, h3720, hc45, hlam, hphi, ht01, ht0b, ht5b, p3722_1, u1elo2]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3713, h3716, hc01, hlam, hphi, p3722_1, u1elo2]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3705, hlam, p3722_1]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3713, hlam, p3722_1]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            rcases p3722_3 (m.d 0 1) (by simp) with h3732 | h3732
                            · linarith only [h0, h3732, hlam]
                            · linarith only [h3539, h3732, hlam]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3539, h3715, h3720, hc45, hlam, hphi, ht01, ht0b, ht5b, p3722_1, u1elo2]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h0, h3539, h3715, h3720, hc45, hlam, hphi, ht01, ht0b, ht5b, p3722_1, u1elo2]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3271, h3539, h3715, h3720, hc45, hlam, hphi, ht01, ht0b, ht5b, p3722_1, u1elo2]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            rcases p3722_3 (m.d 0 1) (by simp) with h3739 | h3739
                            · linarith only [h2837, h3739, hlam]
                            · linarith only [h3539, h3739, hlam]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3539, h3715, h3720, hc45, hlam, hphi, ht01, ht0b, ht5b, p3722_1, u1elo3]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h0, h3539, h3715, h3720, hc45, hlam, hphi, ht01, ht0b, ht5b, p3722_1, u1elo3]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3716, hlam, p3722_1]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            rcases p3722_3 (m.d 0 1) (by simp) with h3746 | h3746
                            · linarith only [h3271, h3746, hlam]
                            · linarith only [h3539, h3746, hlam]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3539, hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3715, hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3717, hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [h3718, hlam, p3722_0]
                          · have p3722_0 := h3722c.1
                            have p3722_1 := h3722c.2.1
                            have p3722_2 := h3722c.2.2.1
                            have p3722_3 := h3722c.2.2.2
                            linarith only [hlam, p3722_0]
                        · linarith only [h0, h3539, h3715, h3720, h3721, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3539, h3713, h3718, h3720, hlam]
                    · linarith only [h0, h3703, h3705, h3719, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h3539, h3704, h3713, h3715, h3718, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h2837, h3539, h3703, h3717, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · linarith only [h0, h3539, h3703, h3705, h3716, hc03, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h3539, h3715, hlam]
      · linarith only [h0, h3539, h3540, h3704, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3762 | h3762
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3763 | h3763
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3764 | h3764
          · linarith only [h0, h3539, h3540, h3764, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3766 | h3766
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3767 | h3767
              · linarith only [h2837, h3539, h3703, h3766, h3767, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3769 | h3769
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3770 | h3770
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3771 | h3771
                    · linarith only [h3763, h3764, h3767, h3771, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3773 | h3773
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3774 | h3774
                        · rcases h1bigk with h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h0, hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h2837, hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3271, hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h2837, h3766, h3773, hc45, hlam, hphi, ht01, ht0b, ht5b, p3775_1, u1elo2]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3764, h3771, hc01, hc34, hlam, hphi, ht12, ht23, p3775_1]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3764, h3771, hc13, hc34, hlam, hphi, p3775_1]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3764, hlam, p3775_1]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            rcases p3775_3 (m.d 0 1) (by simp) with h3785 | h3785
                            · linarith only [h0, h3785, hlam]
                            · linarith only [h3539, h3785, hlam]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3539, h3766, h3773, hc45, hlam, hphi, ht01, ht0b, ht5b, p3775_1, u1elo2]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3763, hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3767, hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            rcases p3775_3 (m.d 0 1) (by simp) with h3792 | h3792
                            · linarith only [h2837, h3792, hlam]
                            · linarith only [h3539, h3792, hlam]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3539, h3766, h3773, hc45, hlam, hphi, ht01, ht0b, ht5b, p3775_1, u1elo3]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3763, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3775_1, u1elo3]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h2837, h3539, h3766, h3773, hc45, hlam, hphi, ht01, ht0b, ht5b, p3775_1, u1elo3]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            rcases p3775_3 (m.d 0 1) (by simp) with h3799 | h3799
                            · linarith only [h3271, h3799, hlam]
                            · linarith only [h3539, h3799, hlam]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3539, hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3766, hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3769, hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [h3770, hlam, p3775_0]
                          · have p3775_0 := h3775c.1
                            have p3775_1 := h3775c.2.1
                            have p3775_2 := h3775c.2.2.1
                            have p3775_3 := h3775c.2.2.2
                            linarith only [hlam, p3775_0]
                        · linarith only [h2837, h3539, h3763, h3764, h3766, h3771, h3773, h3774, hlam]
                      · linarith only [h2837, h3539, h3763, h3764, h3766, h3773, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                  · linarith only [h3271, h3539, h3762, h3766, h3770, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h2837, h3539, h3769, hlam]
            · linarith only [h2837, h3539, h3763, h3766, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3812 | h3812
          · linarith only [h0, h3540, h3812, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3814 | h3814
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3815 | h3815
              · linarith only [h2837, h3539, h3703, h3814, h3815, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3817 | h3817
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3818 | h3818
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3819 | h3819
                    · linarith only [h0, h3539, h3763, h3814, h3815, h3819, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h3539, h3763, h3814, h3819, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h3271, h3762, h3818, hlam]
                · linarith only [h0, h3539, h3763, h3817, hlam]
            · linarith only [h0, h3539, h3814, hlam]
      · linarith only [h3271, h3539, h3762, hlam]

end R2N4
