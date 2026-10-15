import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_68S12

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h649 | h649
  · rcases m.htr 0 1 5 (by decide) (by decide) with h650 | h650
    · rcases m.htr 0 2 3 (by decide) (by decide) with h651 | h651
      · rcases m.htr 0 2 4 (by decide) (by decide) with h652 | h652
        · rcases m.htr 0 3 4 (by decide) (by decide) with h653 | h653
          · rcases m.htr 0 3 5 (by decide) (by decide) with h654 | h654
            · rcases m.htr 0 4 5 (by decide) (by decide) with h655 | h655
              · rcases m.htr 1 2 3 (by decide) (by decide) with h656 | h656
                · rcases m.htr 1 3 5 (by decide) (by decide) with h657 | h657
                  · linarith only [h0, h649, h657, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h649, h654, h656, h657, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h656, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h661 | h661
                · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
                  · linarith only [h0, h649, h662, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h649, h654, h662, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h661, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h653, h654, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h667 | h667
            · rcases m.htr 0 4 5 (by decide) (by decide) with h668 | h668
              · rcases m.htr 1 2 3 (by decide) (by decide) with h669 | h669
                · rcases m.htr 1 3 5 (by decide) (by decide) with h670 | h670
                  · linarith only [h0, h649, h670, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h653, h667, h670, hc13, hc34, hlam, hphi]
                · linarith only [h0, h669, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h653, h667, h668, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h675 | h675
              · rcases m.htr 1 2 3 (by decide) (by decide) with h676 | h676
                · rcases m.htr 1 3 5 (by decide) (by decide) with h677 | h677
                  · linarith only [h0, h649, h667, h677, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h679 | h679
                    · linarith only [h649, h653, h676, h679, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h681 | h681
                      · linarith only [h649, h667, h676, h681, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h683 | h683
                        · rcases h0bigk with h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [hlam, p684_0]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h0, hlam, p684_1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h0, h649, h676, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p684_1, u2elo1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p684_1, u2elo1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h0, h649, h667, h676, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p684_1, u2elo1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, p684_1, u2elo0]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [hlam, p684_0]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h0, h649, h676, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p684_1, u2elo1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h0, h675, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p684_1, u2elo1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h0, h649, h667, h676, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p684_1, u2elo1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h649, hlam, p684_1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h651, hlam, p684_1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [hlam, p684_0]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h653, hlam, p684_1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h667, hlam, p684_1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h650, h676, h677, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p684_1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h652, hlam, p684_0]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h649, h653, h676, hc23, hc34, hlam, hphi, p684_1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [hlam, p684_0]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h0, h649, h652, h667, h676, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p684_1, u2elo1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h650, hlam, p684_0]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h652, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p684_1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h0, h649, h650, h676, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p684_1, u2elo0]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [h675, hlam, p684_1]
                          · have p684_0 := h684c.1
                            have p684_1 := h684c.2.1
                            have p684_2 := h684c.2.2.1
                            have p684_3 := h684c.2.2.2
                            linarith only [hlam, p684_0]
                        · linarith only [h649, h653, h676, h683, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h676, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h712 | h712
                · rcases m.htr 1 3 5 (by decide) (by decide) with h713 | h713
                  · linarith only [h649, h667, h713, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h715 | h715
                    · linarith only [h649, h653, h712, h715, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h717 | h717
                      · linarith only [h649, h667, h712, h717, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h719 | h719
                        · rcases h0bigk with h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [hlam, p720_0]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, hlam, p720_1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, h649, h712, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p720_1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p720_1, u2elo1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p720_1, u2elo1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p720_1, u2elo1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [hlam, p720_0]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, h649, h712, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p720_1, u2elo1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p720_1, u2elo1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, h649, h653, h675, h712, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p720_1, u2elo1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h649, hlam, p720_1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h651, hlam, p720_1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [hlam, p720_0]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h653, hlam, p720_1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h667, hlam, p720_1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h650, h712, h713, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p720_1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h652, hlam, p720_0]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, h649, h650, h675, h712, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p720_1, u2elo1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [hlam, p720_0]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h675, hlam, p720_0]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h650, hlam, p720_0]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, h650, hc02, hlam, hphi, p720_1, u2elo1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, h649, h650, h712, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p720_1, u2elo1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [h0, h650, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p720_1, u2elo1]
                          · have p720_0 := h720c.1
                            have p720_1 := h720c.2.1
                            have p720_2 := h720c.2.2.1
                            have p720_3 := h720c.2.2.2
                            linarith only [hlam, p720_0]
                        · linarith only [h649, h653, h712, h719, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h712, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h748 | h748
          · linarith only [h0, h649, h652, h748, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h750 | h750
            · rcases m.htr 0 4 5 (by decide) (by decide) with h751 | h751
              · rcases m.htr 1 2 3 (by decide) (by decide) with h752 | h752
                · rcases m.htr 1 3 5 (by decide) (by decide) with h753 | h753
                  · linarith only [h0, h649, h652, h753, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h649, h652, h750, h752, h753, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h752, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h651, h652, h751, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h758 | h758
              · rcases m.htr 1 2 3 (by decide) (by decide) with h759 | h759
                · rcases m.htr 1 3 5 (by decide) (by decide) with h760 | h760
                  · linarith only [h0, h649, h750, h760, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h762 | h762
                    · linarith only [h649, h750, h759, h762, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h764 | h764
                      · linarith only [h649, h750, h759, h764, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h766 | h766
                        · rcases h0bigk with h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [hlam, p767_0]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h0, hlam, p767_1]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h0, h652, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p767_1, u2elo3]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h0, h652, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p767_1, u2elo3]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h0, h649, h652, h750, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p767_1, u2elo3]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h652, hc01, hlam, hphi, ht12, p767_1, u2elo3]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [hlam, p767_0]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h649, h652, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p767_1, u2elo3]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h652, hlam, p767_1]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h649, h652, h750, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p767_1, u2elo3]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h649, hlam, p767_1]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h651, hlam, p767_1]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [hlam, p767_0]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h748, hlam, p767_1]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h750, hlam, p767_1]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h650, h759, h760, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p767_1]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h0, h650, h759, h760, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p767_1]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h649, h652, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p767_1, u2elo3]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [hlam, p767_0]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h649, h652, h750, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p767_1, u2elo3]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h650, hlam, p767_0]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h0, h650, h759, h760, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p767_1]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h0, h649, h650, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p767_1, u2elo0]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [h758, hlam, p767_1]
                          · have p767_0 := h767c.1
                            have p767_1 := h767c.2.1
                            have p767_2 := h767c.2.2.1
                            have p767_3 := h767c.2.2.2
                            linarith only [hlam, p767_0]
                        · linarith only [h0, h652, h758, h762, h766, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h0, h759, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h0, h649, h652, h758, hc13, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h0, h649, h651, hlam]
    · linarith only [h649, h650, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h798 | h798
    · rcases m.htr 0 2 3 (by decide) (by decide) with h799 | h799
      · rcases m.htr 0 2 4 (by decide) (by decide) with h800 | h800
        · rcases m.htr 0 3 4 (by decide) (by decide) with h801 | h801
          · rcases m.htr 0 3 5 (by decide) (by decide) with h802 | h802
            · rcases m.htr 0 4 5 (by decide) (by decide) with h803 | h803
              · rcases m.htr 1 2 3 (by decide) (by decide) with h804 | h804
                · rcases m.htr 1 3 5 (by decide) (by decide) with h805 | h805
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h806 | h806
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h807 | h807
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h808 | h808
                        · linarith only [h799, h806, h808, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases h0bigk with h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h0, hlam, p810_1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h649, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h803, h808, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p810_1, u2elo1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, p810_1, u2elo0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h0, h801, h803, h808, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p810_1, u2elo1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h0, h803, h808, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p810_1, u2elo1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h0, h803, h808, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p810_1, u2elo1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h649, hc01, hc13, hlam, hphi, p810_1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h799, hlam, p810_1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h649, h803, h808, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h0, h798, h799, h805, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p810_1, u2elo1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h798, h803, h808, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h800, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h801, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h0, h799, h801, h803, h808, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p810_1, u2elo1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h798, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h798, h799, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p810_1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h802, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h803, hlam, p810_1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hlam, p810_0]
                      · linarith only [h649, h798, h804, h805, h806, h807, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h837 | h837
                      · linarith only [h0, h799, h801, h806, h837, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h649, h798, h804, h805, h837, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h649, h805, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h798, h804, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h842 | h842
                · rcases m.htr 1 3 5 (by decide) (by decide) with h843 | h843
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h844 | h844
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h845 | h845
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h846 | h846
                        · linarith only [h799, h844, h846, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases h0bigk with h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [hlam, p848_0]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h0, hlam, p848_1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h649, hlam, p848_0]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h0, h800, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p848_1, u2elo1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h649, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p848_1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p848_1, u2elo1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [hlam, p848_0]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p848_1, u2elo1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h0, h800, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p848_1, u2elo1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h0, h798, h843, h846, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p848_1, u2elo1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h798, h843, h846, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p848_1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h799, hlam, p848_1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [hlam, p848_0]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h649, h800, h842, h844, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p848_1, u2elo1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h649, h798, h842, h843, h846, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p848_1, u2elo1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h798, h843, h846, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p848_1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h800, hlam, p848_0]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h801, hlam, p848_0]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [hlam, p848_0]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h803, hlam, p848_0]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h798, hlam, p848_0]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h799, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p848_1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h802, hlam, p848_0]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [h649, h798, h842, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p848_1, u2elo1]
                          · have p848_0 := h848c.1
                            have p848_1 := h848c.2.1
                            have p848_2 := h848c.2.2.1
                            have p848_3 := h848c.2.2.2
                            linarith only [hlam, p848_0]
                      · linarith only [h649, h798, h842, h843, h845, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h801, h803, h844, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h649, h843, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h842, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h801, h802, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h879 | h879
            · rcases m.htr 0 4 5 (by decide) (by decide) with h880 | h880
              · rcases m.htr 1 2 3 (by decide) (by decide) with h881 | h881
                · rcases m.htr 1 3 5 (by decide) (by decide) with h882 | h882
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h883 | h883
                    · linarith only [h649, h798, h799, h801, h882, h883, hc02, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h885 | h885
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h886 | h886
                        · rcases h0bigk with h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [hlam, p887_0]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h0, hlam, p887_1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h649, hlam, p887_0]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h649, h801, hlam, p887_1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h649, h798, h882, h886, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p887_1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p887_1, u2elo1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [hlam, p887_0]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p887_1, u2elo1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h0, h649, h798, h801, h882, h886, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p887_1, u2elo1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h0, h798, h882, h886, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p887_1, u2elo1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h798, h882, h886, hc03, hc45, hlam, hphi, ht0b, ht5b, p887_1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h799, hlam, p887_1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [hlam, p887_0]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h801, hlam, p887_1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h798, h801, h882, h886, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p887_1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h0, h798, h800, h882, h886, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p887_1, u2elo1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h800, hlam, p887_0]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h0, h800, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p887_1, u2elo1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [hlam, p887_0]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h0, h798, h800, h882, h886, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p887_1, u2elo1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h798, hlam, p887_0]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h800, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p887_1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h879, hlam, p887_0]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [h880, hlam, p887_1]
                          · have p887_0 := h887c.1
                            have p887_1 := h887c.2.1
                            have p887_2 := h887c.2.2.1
                            have p887_3 := h887c.2.2.2
                            linarith only [hlam, p887_0]
                        · linarith only [h649, h801, h886, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h798, h882, h885, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h649, h882, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h881, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h801, h879, h880, hc35, hlam, hphi, u5elo4]
            · linarith only [h649, h798, h879, hc15, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h919 | h919
          · linarith only [h799, h800, h919, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h921 | h921
            · rcases m.htr 0 4 5 (by decide) (by decide) with h922 | h922
              · rcases m.htr 1 2 3 (by decide) (by decide) with h923 | h923
                · rcases m.htr 1 3 5 (by decide) (by decide) with h924 | h924
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h925 | h925
                    · linarith only [h799, h800, h919, h925, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h927 | h927
                      · linarith only [h799, h800, h927, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · linarith only [h649, h798, h923, h924, h927, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h799, h800, h921, h924, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h923, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h799, h800, h922, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h649, h798, h921, hc15, hlam, hphi, u5elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h934 | h934
        · rcases m.htr 0 3 4 (by decide) (by decide) with h935 | h935
          · rcases m.htr 0 3 5 (by decide) (by decide) with h936 | h936
            · rcases m.htr 0 4 5 (by decide) (by decide) with h937 | h937
              · rcases m.htr 1 2 3 (by decide) (by decide) with h938 | h938
                · linarith only [h799, h938, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h798, h938, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h941 | h941
                · linarith only [h799, h934, h941, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h798, h941, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h799, h934, h936, hc24, hlam, hphi, ht45, u5elo3]
          · linarith only [h799, h934, h935, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h946 | h946
          · rcases m.htr 0 3 5 (by decide) (by decide) with h947 | h947
            · rcases m.htr 0 4 5 (by decide) (by decide) with h948 | h948
              · rcases m.htr 1 2 3 (by decide) (by decide) with h949 | h949
                · linarith only [h0, h798, h799, h949, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h798, h949, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h0, h798, h934, h948, hc15, hlam, hphi, u5elo4]
            · linarith only [h0, h798, h934, h946, h947, hc15, hlam, hphi, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h954 | h954
            · rcases m.htr 0 4 5 (by decide) (by decide) with h955 | h955
              · rcases m.htr 1 2 3 (by decide) (by decide) with h956 | h956
                · linarith only [h0, h798, h799, h956, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h798, h956, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h946, h954, h955, hc35, hlam, hphi, u5elo4]
            · linarith only [h0, h798, h799, h954, hc15, hlam, hphi, u5elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h961 | h961
      · rcases m.htr 0 2 4 (by decide) (by decide) with h962 | h962
        · rcases m.htr 0 3 4 (by decide) (by decide) with h963 | h963
          · rcases m.htr 0 3 5 (by decide) (by decide) with h964 | h964
            · rcases m.htr 0 4 5 (by decide) (by decide) with h965 | h965
              · rcases m.htr 1 2 3 (by decide) (by decide) with h966 | h966
                · rcases m.htr 1 3 5 (by decide) (by decide) with h967 | h967
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h968 | h968
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h969 | h969
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h970 | h970
                        · linarith only [h961, h968, h970, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases h0bigk with h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [hlam, p972_0]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h0, hlam, p972_1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h649, hlam, p972_0]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h798, hc04, hlam, hphi, ht45, p972_1, u5elo1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h798, hlam, p972_1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p972_1, u2elo1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [hlam, p972_0]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p972_1, u2elo1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h0, h965, h970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p972_1, u2elo1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h0, h965, h970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p972_1, u2elo1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h649, hc01, hc13, hlam, hphi, p972_1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h961, hlam, p972_1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [hlam, p972_0]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h0, h961, h965, h970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p972_1, u2elo1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h0, h961, h965, h970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p972_1, u2elo1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h0, h962, hc01, hlam, hphi, ht12, p972_1, u2elo1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h962, hlam, p972_0]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h963, hlam, p972_0]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [hlam, p972_0]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h0, h961, h963, h965, h970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p972_1, u2elo1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p972_1, u5elo0]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h798, h961, h963, h965, h970, hc34, hlam, hphi, ht45, p972_1, u5elo1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h964, hlam, p972_0]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [h965, hlam, p972_1]
                          · have p972_0 := h972c.1
                            have p972_1 := h972c.2.1
                            have p972_2 := h972c.2.2.1
                            have p972_3 := h972c.2.2.2
                            linarith only [hlam, p972_0]
                      · linarith only [h0, h961, h964, h968, h969, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h999 | h999
                      · linarith only [h0, h961, h963, h968, h999, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1001 | h1001
                        · rcases h0bigk with h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [hlam, p1002_0]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h0, hlam, p1002_1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h649, hlam, p1002_0]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1002_1, u2elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h798, hlam, p1002_1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p1002_1, u2elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [hlam, p1002_0]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h0, h1001, h963, h999, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1002_1, u2elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1002_1, u2elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1002_1, u2elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h649, h966, hc01, hlam, hphi, ht12, p1002_1, u2elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h961, hlam, p1002_1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [hlam, p1002_0]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h649, h962, h966, h968, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1002_1, u2elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h649, h798, h966, hc01, hlam, hphi, ht12, p1002_1, u2elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h0, h962, hc01, hlam, hphi, ht12, p1002_1, u2elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h962, hlam, p1002_0]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h963, hlam, p1002_0]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [hlam, p1002_0]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h649, h963, h964, h966, h999, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1002_1, u2elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1002_1, u5elo0]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h1001, h649, h798, h963, h966, h999, hc02, hc23, hlam, hphi, ht34, ht45, p1002_1, u2elo1, u5elo1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h964, hlam, p1002_0]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [h965, hlam, p1002_1]
                          · have p1002_0 := h1002c.1
                            have p1002_1 := h1002c.2.1
                            have p1002_2 := h1002c.2.2.1
                            have p1002_3 := h1002c.2.2.2
                            linarith only [hlam, p1002_0]
                        · linarith only [h0, h1001, h961, h963, h965, h968, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h649, h963, h965, h967, hc45, hlam, hphi, u5elo3]
                · linarith only [h0, h966, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1031 | h1031
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1032 | h1032
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1033 | h1033
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1034 | h1034
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1035 | h1035
                        · linarith only [h1033, h1035, h961, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
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
                            linarith only [h0, hlam, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h649, hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1037_1, u2elo1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h798, hlam, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p1037_1, u2elo1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1037_1, u2elo1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1037_1, u2elo1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1, u2elo1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h649, hc01, hc13, hlam, hphi, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h961, hlam, p1037_1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h0, h961, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1037_1, u2elo1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h0, h798, h961, hc01, hlam, hphi, ht12, p1037_1, u2elo1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h0, h962, hc01, hlam, hphi, ht12, p1037_1, u2elo1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h962, hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h963, hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h965, hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1037_1, u5elo0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h1034, h1035, h798, h961, hc34, hlam, hphi, ht45, p1037_1, u5elo1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h964, hlam, p1037_0]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [h798, hc04, hlam, hphi, ht45, p1037_1, u5elo1]
                          · have p1037_0 := h1037c.1
                            have p1037_1 := h1037c.2.1
                            have p1037_2 := h1037c.2.2.1
                            have p1037_3 := h1037c.2.2.2
                            linarith only [hlam, p1037_0]
                      · linarith only [h0, h1033, h1034, h961, h964, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1033, h963, h965, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h1032, h649, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h1031, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h963, h964, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1068 | h1068
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1069 | h1069
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1070 | h1070
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1071 | h1071
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1072 | h1072
                    · linarith only [h1068, h1072, h961, h963, hc02, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1074 | h1074
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1075 | h1075
                        · rcases h0bigk with h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [hlam, p1076_0]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h0, hlam, p1076_1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h649, hlam, p1076_0]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h1074, h1075, h961, h963, hc01, hc45, hlam, hphi, ht0b, ht5b, p1076_1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h798, hlam, p1076_1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p1076_1, u2elo1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [hlam, p1076_0]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h0, h1074, h1075, h961, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1076_1, u2elo1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h0, h1074, h1075, h961, h963, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1076_1, u2elo1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1076_1, u2elo1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h963, hc01, hc34, hlam, hphi, ht12, ht23, p1076_1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h961, hlam, p1076_1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [hlam, p1076_0]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h963, hlam, p1076_1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h0, h798, h962, h963, hc01, hlam, hphi, ht12, p1076_1, u2elo1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h0, h962, hc01, hlam, hphi, ht12, p1076_1, u2elo1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h962, hlam, p1076_0]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h0, h962, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1076_1, u2elo1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [hlam, p1076_0]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h0, h798, h962, hc01, hlam, hphi, ht12, p1076_1, u2elo1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1076_1, u5elo0]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h1068, h1072, h1074, h1075, h962, hc03, hc45, hlam, hphi, ht0b, ht5b, p1076_1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h1068, hlam, p1076_0]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [h1069, hlam, p1076_1]
                          · have p1076_0 := h1076c.1
                            have p1076_1 := h1076c.2.1
                            have p1076_2 := h1076c.2.2.1
                            have p1076_3 := h1076c.2.2.2
                            linarith only [hlam, p1076_0]
                        · linarith only [h1075, h963, hc03, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h1068, h1074, h963, hc23, hc34, hlam, hphi]
                  · linarith only [h1068, h1071, h963, hc13, hc34, hlam, hphi]
                · linarith only [h0, h1070, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1068, h1069, h963, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1107 | h1107
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1108 | h1108
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1109 | h1109
                  · linarith only [h1068, h1108, h1109, h649, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h1109, h649, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h1108, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1113 | h1113
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1114 | h1114
                  · linarith only [h1068, h1113, h1114, h649, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h1114, h649, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h1113, h961, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1118 | h1118
          · linarith only [h1118, h961, h962, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1120 | h1120
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1121 | h1121
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1122 | h1122
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1123 | h1123
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1124 | h1124
                    · linarith only [h1118, h1124, h961, h962, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1126 | h1126
                      · linarith only [h1126, h961, h962, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · linarith only [h1120, h1126, h961, h962, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h1120, h1123, h961, h962, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1122, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1121, h961, h962, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1132 | h1132
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1133 | h1133
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1134 | h1134
                  · linarith only [h1120, h1133, h1134, h649, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h1134, h649, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h1133, h961, h962, hc12, hlam, hphi, u2elo3]
              · linarith only [h1132, h961, h962, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1139 | h1139
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1140 | h1140
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1141 | h1141
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1142 | h1142
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1143 | h1143
                · linarith only [h1139, h1143, h961, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h1143, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1146 | h1146
                · linarith only [h1139, h1146, h961, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h1146, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1139, h1141, h961, hc24, hlam, hphi, ht45, u5elo3]
          · linarith only [h1139, h1140, h961, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1151 | h1151
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1152 | h1152
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1153 | h1153
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1154 | h1154
                · linarith only [h1154, h961, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1154, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1157 | h1157
                · linarith only [h0, h1157, h961, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1157, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1151, h1152, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1161 | h1161
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1162 | h1162
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1163 | h1163
                · linarith only [h0, h1163, h961, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1163, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1151, h1161, h1162, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1167 | h1167
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1168 | h1168
                · linarith only [h0, h1168, h961, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1168, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1171 | h1171
                · linarith only [h0, h1171, h961, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1171, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_0_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_0_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
