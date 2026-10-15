import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_56S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4024000 in
set_option maxHeartbeats 4024000 in
theorem r1l7_14_25_L_0_H_I_x0_x0_x1 (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h656 | h656
  · rcases m.htr 0 4 5 (by decide) (by decide) with h657 | h657
    · rcases m.htr 1 2 3 (by decide) (by decide) with h658 | h658
      · rcases m.htr 1 2 5 (by decide) (by decide) with h659 | h659
        · linarith only [h1, h2, h659, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h661 | h661
          · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
            · linarith only [h658, h659, h662, hlam]
            · linarith only [h656, h657, h661, h662, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h665 | h665
            · linarith only [h658, h659, h661, h665, hc23, hlam, hphi, ht34, u4elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h667 | h667
              · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                · linarith only [h658, h659, h667, h668, hc34, hlam, hphi, u4elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h670 | h670
                  · linarith only [h658, h659, h665, h670, hlam]
                  · linarith only [h656, h657, h658, h659, h670, hc23, hlam, hphi, ht34, u4elo0]
              · linarith only [h657, h667, hc14, hlam, hphi, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h674 | h674
        · linarith only [h2, h658, h674, hc02, hc23, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h676 | h676
          · rcases m.htr 1 3 5 (by decide) (by decide) with h677 | h677
            · rcases m.htr 1 4 5 (by decide) (by decide) with h678 | h678
              · rcases m.htr 2 3 4 (by decide) (by decide) with h679 | h679
                · rcases m.htr 2 3 5 (by decide) (by decide) with h680 | h680
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h681 | h681
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h682 | h682
                      · rcases h5bigk with h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [hlam, p683_0]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h2, h681, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p683_1, u4elo2]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h2, hlam, p683_0]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h2, h681, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p683_1, u4elo2]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h2, h681, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p683_1, u4elo2]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h1, hlam, p683_0]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [hlam, p683_0]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h674, hlam, p683_0]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p683_1]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h1, h2, h681, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p683_1, u4elo2]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h681, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p683_1, u4elo2]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h681, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p683_1, u4elo2]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [hlam, p683_0]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h681, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p683_1, u4elo2]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h681, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p683_1, u4elo2]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h656, hlam, p683_1]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h677, hlam, p683_1]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h680, hlam, p683_0]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [hlam, p683_0]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h656, hc03, hc45, hlam, hphi, ht0b, ht5b, p683_1]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h657, hlam, p683_1]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h678, hlam, p683_1]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h681, hlam, p683_1]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [h682, hlam, p683_1]
                        · have p683_0 := h683c.1
                          have p683_1 := h683c.2.1
                          have p683_2 := h683c.2.2.1
                          have p683_3 := h683c.2.2.2
                          linarith only [hlam, p683_0]
                      · linarith only [h657, h682, hc34, hlam, hphi, u4elo0]
                    · linarith only [h678, h681, hc24, hlam, hphi, u4elo1]
                  · linarith only [h1, h657, h658, h677, h680, hc12, hlam, hphi, ht23, ht34, u4elo0]
                · linarith only [h658, h676, h679, hlam]
              · linarith only [h657, h678, hc14, hlam, hphi, u4elo0]
            · linarith only [h656, h657, h676, h677, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h715 | h715
            · rcases m.htr 1 4 5 (by decide) (by decide) with h716 | h716
              · rcases m.htr 2 3 4 (by decide) (by decide) with h717 | h717
                · rcases m.htr 2 3 5 (by decide) (by decide) with h718 | h718
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h719 | h719
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h720 | h720
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
                          linarith only [h2, h719, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p721_1, u4elo2]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h2, hlam, p721_0]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h2, h719, h720, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p721_1, u4elo2]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h2, h719, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p721_1, u4elo2]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h1, hlam, p721_0]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [hlam, p721_0]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h674, hlam, p721_0]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h1, h720, hc01, hc45, hlam, hphi, ht0b, ht5b, p721_1]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h676, h715, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p721_1, u4elo1]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h719, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p721_1, u4elo2]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h719, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p721_1, u4elo2]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [hlam, p721_0]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h719, h720, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p721_1, u4elo2]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h719, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p721_1, u4elo2]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h656, hlam, p721_1]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h715, hlam, p721_1]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h718, hlam, p721_0]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [hlam, p721_0]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h656, hc03, hc45, hlam, hphi, ht0b, ht5b, p721_1]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h657, hlam, p721_1]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h716, hlam, p721_1]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h719, hlam, p721_1]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [h720, hlam, p721_1]
                        · have p721_0 := h721c.1
                          have p721_1 := h721c.2.1
                          have p721_2 := h721c.2.2.1
                          have p721_3 := h721c.2.2.2
                          linarith only [hlam, p721_0]
                      · linarith only [h676, h720, hc13, hlam, hphi, ht34, u4elo4]
                    · linarith only [h657, h719, hc24, hlam, hphi, u4elo0]
                  · linarith only [h676, h715, h717, h718, hlam]
                · linarith only [h658, h717, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h657, h716, hc14, hlam, hphi, u4elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h752 | h752
              · rcases m.htr 2 3 4 (by decide) (by decide) with h753 | h753
                · rcases m.htr 2 3 5 (by decide) (by decide) with h754 | h754
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h755 | h755
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h756 | h756
                      · rcases h5bigk with h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [hlam, p757_0]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h2, h755, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p757_1, u4elo2]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h2, hlam, p757_0]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h2, h658, h715, h755, hc12, hlam, hphi, ht23, ht34, p757_1, u4elo2]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h2, h755, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p757_1, u4elo2]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h1, hlam, p757_0]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [hlam, p757_0]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h674, hlam, p757_0]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h715, hlam, p757_0]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p757_1]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h755, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p757_1, u4elo2]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h755, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p757_1, u4elo2]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [hlam, p757_0]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h658, h715, h755, hc12, hlam, hphi, ht23, ht34, p757_1, u4elo2]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h755, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p757_1, u4elo2]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h656, hlam, p757_1]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h658, h715, hc12, hc35, hlam, hphi, ht23, p757_1]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h754, hlam, p757_0]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [hlam, p757_0]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h2, h656, h755, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p757_1, u4elo2]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h657, hlam, p757_1]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h752, hlam, p757_1]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h755, hlam, p757_1]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [h756, hlam, p757_1]
                        · have p757_0 := h757c.1
                          have p757_1 := h757c.2.1
                          have p757_2 := h757c.2.2.1
                          have p757_3 := h757c.2.2.2
                          linarith only [hlam, p757_0]
                      · linarith only [h752, h756, hc34, hlam, hphi, u4elo1]
                    · linarith only [h657, h676, h753, h755, hc14, hlam, hphi, u4elo0]
                  · linarith only [h656, h676, h752, h753, h754, hc03, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h658, h753, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h657, h752, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
      · rcases m.htr 1 2 5 (by decide) (by decide) with h789 | h789
        · linarith only [h1, h2, h789, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h791 | h791
          · rcases m.htr 1 3 5 (by decide) (by decide) with h792 | h792
            · linarith only [h788, h789, h792, hlam]
            · linarith only [h656, h657, h791, h792, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h795 | h795
            · linarith only [h0, h657, h788, h789, h791, h795, hc23, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h797 | h797
              · linarith only [h0, h657, h797, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
                · linarith only [h1, h657, h788, h789, h799, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h801 | h801
                  · linarith only [h788, h789, h795, h801, hlam]
                  · linarith only [h2, h656, h801, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h804 | h804
        · linarith only [h2, h788, h804, hc02, hc23, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h806 | h806
          · rcases m.htr 1 3 5 (by decide) (by decide) with h807 | h807
            · rcases m.htr 1 4 5 (by decide) (by decide) with h808 | h808
              · linarith only [h0, h657, h808, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h810 | h810
                · rcases m.htr 2 3 5 (by decide) (by decide) with h811 | h811
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h812 | h812
                    · linarith only [h657, h812, hc04, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h814 | h814
                      · linarith only [h0, h804, h806, h812, h814, hc12, hlam, hphi, ht23, ht34, u4elo0]
                      · rcases h5bigk with h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h657, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p816_1, u4elo4]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h2, hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h657, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p816_1, u4elo4]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h657, hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h1, hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h804, hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p816_1]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h808, hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h2, hc02, hc25, hlam, hphi, p816_1]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h804, hc12, hc25, hlam, hphi, p816_1]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h812, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p816_1, u4elo4]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h812, hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h656, hlam, p816_1]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h807, hlam, p816_1]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h811, hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h814, hlam, p816_0]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h657, hc04, hlam, hphi, p816_1, u4elo4]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [h804, hc12, hlam, hphi, ht23, ht34, p816_1, u4elo4]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p816_1, u4elo4]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p816_1, u4elo4]
                        · have p816_0 := h816c.1
                          have p816_1 := h816c.2.1
                          have p816_2 := h816c.2.2.1
                          have p816_3 := h816c.2.2.2
                          linarith only [hlam, p816_0]
                  · linarith only [h656, h657, h788, h811, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h0, h788, h806, h810, hc12, hlam, hphi, ht23, ht34, u4elo0]
            · linarith only [h656, h657, h806, h807, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h845 | h845
            · rcases m.htr 1 4 5 (by decide) (by decide) with h846 | h846
              · linarith only [h0, h657, h846, hlam]
              · linarith only [h806, h845, h846, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h849 | h849
              · linarith only [h657, h849, hc04, hlam, hphi, u4elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h851 | h851
                · rcases m.htr 2 3 5 (by decide) (by decide) with h852 | h852
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h853 | h853
                    · linarith only [h656, h657, h788, h845, h853, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h788, h806, h851, h853, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h656, h657, h788, h806, h851, h852, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h788, h851, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h858 | h858
    · rcases m.htr 1 2 3 (by decide) (by decide) with h859 | h859
      · rcases m.htr 1 2 5 (by decide) (by decide) with h860 | h860
        · linarith only [h1, h2, h860, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h862 | h862
          · rcases m.htr 1 3 5 (by decide) (by decide) with h863 | h863
            · linarith only [h1, h656, h859, h860, h863, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h865 | h865
              · linarith only [h859, h860, h862, h865, hlam]
              · linarith only [h858, h865, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h868 | h868
            · linarith only [h656, h862, h868, hc03, hlam, hphi, ht34, u4elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h870 | h870
              · rcases m.htr 2 3 4 (by decide) (by decide) with h871 | h871
                · linarith only [h859, h860, h862, h870, h871, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h873 | h873
                  · linarith only [h1, h656, h859, h860, h873, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h875 | h875
                    · linarith only [h859, h860, h875, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h870, h875, hc24, hlam, hphi, u4elo0]
              · linarith only [h858, h870, hc14, hlam, hphi, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h879 | h879
        · linarith only [h2, h859, h879, hc02, hc23, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h881 | h881
          · rcases m.htr 1 3 5 (by decide) (by decide) with h882 | h882
            · linarith only [h1, h656, h882, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h884 | h884
              · linarith only [h881, h882, h884, hlam]
              · linarith only [h858, h884, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h887 | h887
            · linarith only [h656, h881, h887, hc03, hlam, hphi, ht34, u4elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h889 | h889
              · rcases m.htr 2 3 4 (by decide) (by decide) with h890 | h890
                · rcases m.htr 2 3 5 (by decide) (by decide) with h891 | h891
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h892 | h892
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h893 | h893
                      · rcases h5bigk with h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [hlam, p894_0]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h656, h859, h887, h891, h892, hc12, hlam, hphi, ht23, ht34, p894_1, u4elo2]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h2, hlam, p894_0]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h656, hlam, p894_0]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h656, h891, h892, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p894_1, u4elo2]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h1, hlam, p894_0]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [hlam, p894_0]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h879, hlam, p894_0]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h887, hlam, p894_0]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p894_1]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h892, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p894_1, u4elo2]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h892, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p894_1, u4elo2]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [hlam, p894_0]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h892, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p894_1, u4elo2]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h892, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p894_1, u4elo2]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h1, h859, h887, hc12, hc35, hlam, hphi, ht23, p894_1]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h859, h887, hc12, hc35, hlam, hphi, ht23, p894_1]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h891, hlam, p894_0]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [hlam, p894_0]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h891, h892, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p894_1, u4elo2]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h858, hlam, p894_1]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h889, hlam, p894_1]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h892, hlam, p894_1]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [h893, hlam, p894_1]
                        · have p894_0 := h894c.1
                          have p894_1 := h894c.2.1
                          have p894_2 := h894c.2.2.1
                          have p894_3 := h894c.2.2.2
                          linarith only [hlam, p894_0]
                      · linarith only [h889, h893, hc34, hlam, hphi, u4elo1]
                    · linarith only [h858, h881, h890, h892, hc14, hlam, hphi, u4elo0]
                  · linarith only [h859, h881, h890, h891, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h859, h890, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h858, h889, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h925 | h925
      · rcases m.htr 1 2 5 (by decide) (by decide) with h926 | h926
        · linarith only [h1, h2, h926, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h928 | h928
          · rcases m.htr 1 3 5 (by decide) (by decide) with h929 | h929
            · linarith only [h1, h656, h925, h926, h929, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h931 | h931
              · linarith only [h858, h931, hc04, hlam, hphi, u4elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h933 | h933
                · linarith only [h1, h858, h925, h926, h933, hc34, hlam, hphi, u4elo4]
                · linarith only [h1, h858, h925, h926, h928, h933, hc23, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h936 | h936
            · linarith only [h0, h656, h858, h928, h936, hc03, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h938 | h938
              · linarith only [h0, h858, h938, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h940 | h940
                · linarith only [h1, h858, h925, h926, h940, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h942 | h942
                  · linarith only [h1, h656, h925, h926, h942, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h944 | h944
                    · linarith only [h858, h944, hc04, hlam, hphi, u4elo2]
                    · linarith only [h925, h926, h944, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h947 | h947
        · linarith only [h2, h925, h947, hc02, hc23, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h949 | h949
          · rcases m.htr 1 3 5 (by decide) (by decide) with h950 | h950
            · linarith only [h1, h656, h950, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h952 | h952
              · linarith only [h0, h858, h952, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h954 | h954
                · rcases m.htr 2 3 5 (by decide) (by decide) with h955 | h955
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h956 | h956
                    · linarith only [h1, h858, h949, h950, h956, hc34, hlam, hphi, u4elo2]
                    · linarith only [h949, h950, h955, h956, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h959 | h959
                    · linarith only [h0, h858, h949, h959, hc34, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h961 | h961
                      · linarith only [h1, h2, h949, h950, h959, h961, hlam]
                      · linarith only [h925, h955, h961, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h1, h2, h925, h949, h950, h954, hc12, hc25, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h965 | h965
            · linarith only [h0, h656, h858, h949, h965, hc03, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h967 | h967
              · linarith only [h0, h858, h967, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h969 | h969
                · rcases m.htr 2 3 5 (by decide) (by decide) with h970 | h970
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h971 | h971
                    · linarith only [h858, h971, hc04, hlam, hphi, u4elo2]
                    · linarith only [h925, h949, h969, h971, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h925, h949, h969, h970, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h925, h969, hc12, hlam, hphi, ht23, ht34, u4elo3]

set_option maxHeartbeats 4024000 in
set_option maxHeartbeats 4024000 in
theorem r1l7_14_25_L_0_H_I_x0_x0 (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_14_25_L_0_H_I_x0_x0_x0 m hb4 hb5 h0 h1 h2
  · exact r1l7_14_25_L_0_H_I_x0_x0_x1 m hb4 hb5 h0 h1 h2

set_option maxHeartbeats 4024000 in
set_option maxHeartbeats 4024000 in
theorem r1l7_14_25_L_0_H_I_x0_x1 (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h1 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h976 | h976
  · rcases m.htr 0 3 5 (by decide) (by decide) with h977 | h977
    · rcases m.htr 0 4 5 (by decide) (by decide) with h978 | h978
      · linarith only [h0, h1, h978, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h980 | h980
        · rcases m.htr 1 2 5 (by decide) (by decide) with h981 | h981
          · rcases m.htr 1 3 4 (by decide) (by decide) with h982 | h982
            · rcases m.htr 1 3 5 (by decide) (by decide) with h983 | h983
              · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                · linarith only [h978, h984, hc04, hlam, hphi, u4elo1]
                · linarith only [h0, h1, h984, hc14, hlam, hphi, u4elo4]
              · linarith only [h977, h978, h982, h983, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h988 | h988
              · linarith only [h0, h1, h982, h988, hlam]
              · linarith only [h0, h1, h977, h978, h982, h988, hc13, hlam, hphi, ht34, u4elo4]
          · linarith only [h976, h978, h980, h981, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h992 | h992
          · rcases m.htr 1 3 4 (by decide) (by decide) with h993 | h993
            · rcases m.htr 1 3 5 (by decide) (by decide) with h994 | h994
              · rcases m.htr 1 4 5 (by decide) (by decide) with h995 | h995
                · linarith only [h0, h1, h978, h980, h992, h995, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1, h993, h995, hc34, hlam, hphi, u4elo4]
              · linarith only [h0, h1, h977, h978, h980, h992, h993, h994, hc34, hlam, hphi, u4elo4]
            · linarith only [h0, h1, h980, h992, h993, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h1, h976, h978, h992, hc14, hlam, hphi, u4elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1001 | h1001
      · linarith only [h0, h1, h1001, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1003 | h1003
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1004 | h1004
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1005 | h1005
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1006 | h1006
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1007 | h1007
                · linarith only [h1001, h1007, hc04, hlam, hphi, u4elo1]
                · linarith only [h0, h1, h1005, h1007, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1010 | h1010
                · linarith only [h1001, h1010, hc04, hlam, hphi, u4elo1]
                · linarith only [h0, h1, h1005, h1010, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1013 | h1013
              · linarith only [h0, h1, h1005, h1013, h977, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1015 | h1015
                · linarith only [h0, h1, h1001, h1015, hlam]
                · linarith only [h0, h1, h1005, h1015, hc13, hlam, hphi, ht34, u4elo4]
          · linarith only [h1001, h1003, h1004, h976, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1019 | h1019
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1020 | h1020
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1021 | h1021
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1022 | h1022
                · linarith only [h0, h1, h1003, h1019, h1022, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h1, h1020, h1022, hc34, hlam, hphi, u4elo4]
              · linarith only [h1003, h1019, h1021, hlam]
            · linarith only [h1, h1003, h1019, h1020, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h0, h1, h1001, h1019, h976, hc14, hlam, hphi, u4elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1028 | h1028
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1029 | h1029
      · linarith only [h0, h1, h1029, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1031 | h1031
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1032 | h1032
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1033 | h1033
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1034 | h1034
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1035 | h1035
                · linarith only [h1029, h1035, hc04, hlam, hphi, u4elo1]
                · linarith only [h0, h1, h1033, h1035, hc34, hlam, hphi, u4elo4]
              · linarith only [h1028, h1029, h1033, h1034, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1039 | h1039
              · linarith only [h0, h1, h1033, h1039, hlam]
              · linarith only [h0, h1, h1028, h1029, h1033, h1039, hc13, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1042 | h1042
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1043 | h1043
              · linarith only [h1031, h1032, h1043, hlam]
              · linarith only [h1028, h1029, h1042, h1043, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1046 | h1046
              · linarith only [h0, h1, h1042, h1046, hlam]
              · linarith only [h0, h1, h1028, h1029, h1042, h1046, hc13, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1049 | h1049
          · linarith only [h1031, h1049, h976, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1051 | h1051
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1052 | h1052
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1053 | h1053
                · linarith only [h0, h1, h1029, h1053, hlam]
                · linarith only [h0, h1, h1051, h1053, hc34, hlam, hphi, u4elo4]
              · linarith only [h1028, h1029, h1051, h1052, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1057 | h1057
              · linarith only [h0, h1, h1051, h1057, hlam]
              · linarith only [h0, h1, h1028, h1029, h1031, h1051, h1057, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1060 | h1060
      · linarith only [h0, h1, h1060, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1062 | h1062
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1063 | h1063
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1064 | h1064
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1065 | h1065
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1066 | h1066
                · linarith only [h1060, h1066, hc04, hlam, hphi, u4elo1]
                · linarith only [h0, h1, h1064, h1066, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1069 | h1069
                · linarith only [h0, h1, h1060, h1069, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h1, h1064, h1069, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1072 | h1072
              · linarith only [h0, h1, h1028, h1064, h1072, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1074 | h1074
                · linarith only [h0, h1, h1060, h1074, hlam]
                · linarith only [h0, h1, h1064, h1074, hc13, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1077 | h1077
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1078 | h1078
              · linarith only [h1062, h1063, h1078, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1080 | h1080
                · linarith only [h0, h1060, h1080, hlam]
                · linarith only [h0, h1, h1080, hc14, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1083 | h1083
              · linarith only [h0, h1, h1028, h1077, h1083, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1085 | h1085
                · linarith only [h0, h1, h1060, h1085, hlam]
                · linarith only [h0, h1, h1077, h1085, hc13, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1088 | h1088
          · linarith only [h1062, h1088, h976, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1090 | h1090
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1091 | h1091
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1092 | h1092
                · linarith only [h1060, h1092, hc04, hlam, hphi, u4elo1]
                · linarith only [h0, h1, h1092, hc14, hlam, hphi, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1095 | h1095
                · linarith only [h0, h1, h1060, h1095, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h1, h1090, h1095, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1098 | h1098
              · linarith only [h0, h1, h1028, h1090, h1098, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1100 | h1100
                · linarith only [h0, h1, h1060, h1100, hlam]
                · linarith only [h0, h1, h1062, h1090, h1100, hc12, hlam, hphi, ht23, ht34, u4elo4]

set_option maxHeartbeats 4024000 in
set_option maxHeartbeats 4024000 in
theorem r1l7_14_25_L_0_H_I_x0 (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_14_25_L_0_H_I_x0_x0 m hb4 hb5 h0 h1
  · exact r1l7_14_25_L_0_H_I_x0_x1 m hb4 hb5 h0 h1

set_option maxHeartbeats 4024000 in
set_option maxHeartbeats 4024000 in
theorem r1l7_14_25_L_0_H_I_x1_x0 (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1103 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1104 | h1104
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1105 | h1105
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1106 | h1106
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1107 | h1107
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1108 | h1108
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1109 | h1109
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1110 | h1110
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1111 | h1111
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1112 | h1112
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1113 | h1113
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1114 | h1114
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1115 | h1115
                        · rcases h5bigk with h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [hlam, p1116_0]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h0, h1103, h1108, h1113, h1115, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1116_1, u4elo1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h0, h1103, h1113, h1115, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1116_1, u4elo1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h0, h1103, h1115, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1116_1, u4elo1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h0, h1103, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1116_1, u4elo1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1103, hlam, p1116_0]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [hlam, p1116_0]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h0, h1103, h1113, h1115, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1116_1, u4elo1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h0, h1103, h1115, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1116_1, u4elo1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h0, h1103, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1116_1, u4elo1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1104, hlam, p1116_1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1108, hlam, p1116_1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [hlam, p1116_0]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1104, h1115, hc02, hc45, hlam, hphi, ht0b, ht5b, p1116_1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h0, h1103, h1108, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1116_1, u4elo1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1105, hlam, p1116_1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1110, hlam, p1116_1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1113, hlam, p1116_0]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [hlam, p1116_0]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1105, hc03, hc45, hlam, hphi, ht0b, ht5b, p1116_1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1106, hlam, p1116_1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1111, hlam, p1116_1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1114, hlam, p1116_1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [h1115, hlam, p1116_1]
                          · have p1116_0 := h1116c.1
                            have p1116_1 := h1116c.2.1
                            have p1116_2 := h1116c.2.2.1
                            have p1116_3 := h1116c.2.2.2
                            linarith only [hlam, p1116_0]
                        · linarith only [h1106, h1115, hc34, hlam, hphi, u4elo0]
                      · linarith only [h0, h1103, h1111, h1112, h1114, hc34, hlam, hphi, u4elo1]
                    · linarith only [h0, h1103, h1105, h1113, hc23, hlam, hphi, ht34, u4elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1145 | h1145
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1146 | h1146
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1147 | h1147
                        · rcases h5bigk with h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [hlam, p1148_0]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h0, h1103, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1148_1, u4elo1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h0, h1103, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1148_1, u4elo1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h0, h1103, h1147, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1148_1, u4elo1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h0, h1103, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1148_1, u4elo1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1103, hlam, p1148_0]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [hlam, p1148_0]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h0, h1103, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1148_1, u4elo1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h0, h1103, h1147, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1148_1, u4elo1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h0, h1103, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1148_1, u4elo1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1104, hlam, p1148_1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1108, hlam, p1148_1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [hlam, p1148_0]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1104, h1147, hc02, hc45, hlam, hphi, ht0b, ht5b, p1148_1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h0, h1103, h1108, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1148_1, u4elo1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1105, hlam, p1148_1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1110, hlam, p1148_1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1145, hlam, p1148_0]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [hlam, p1148_0]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1109, h1112, h1145, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1148_1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1106, hlam, p1148_1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1111, hlam, p1148_1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1146, hlam, p1148_1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [h1147, hlam, p1148_1]
                          · have p1148_0 := h1148c.1
                            have p1148_1 := h1148c.2.1
                            have p1148_2 := h1148c.2.2.1
                            have p1148_3 := h1148c.2.2.2
                            linarith only [hlam, p1148_0]
                        · linarith only [h1112, h1147, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1103, h1111, h1146, hc24, hlam, hphi, u4elo1]
                    · linarith only [h0, h1103, h1105, h1145, hc23, hlam, hphi, ht34, u4elo1]
                · linarith only [h0, h1111, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h0, h1103, h1105, h1110, hc13, hlam, hphi, ht34, u4elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1179 | h1179
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1180 | h1180
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1181 | h1181
                  · linarith only [h0, h1107, h1109, h1181, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1183 | h1183
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1184 | h1184
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1185 | h1185
                        · rcases h5bigk with h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h0, h1103, h1108, h1109, h1183, h1185, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1186_1, u4elo3]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h0, h1103, h1109, h1183, h1185, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1186_1, u4elo3]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h0, h1103, h1109, h1185, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1186_1, u4elo3]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h0, h1103, h1109, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1186_1, u4elo3]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1103, hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h0, h1103, h1109, h1183, h1185, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1186_1, u4elo3]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h0, h1103, h1109, h1185, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1186_1, u4elo3]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h0, h1103, h1109, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1186_1, u4elo3]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1104, hlam, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1108, hlam, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1104, h1185, hc02, hc45, hlam, hphi, ht0b, ht5b, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h0, h1103, h1108, h1109, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1186_1, u4elo3]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1105, hlam, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1179, hlam, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1183, hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1107, h1183, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1106, hlam, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1180, hlam, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1184, hlam, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1185, hlam, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [hlam, p1186_0]
                        · linarith only [h0, h1109, h1185, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h0, h1103, h1180, h1184, hc24, hlam, hphi, u4elo1]
                    · linarith only [h0, h1103, h1105, h1109, h1183, hc23, hlam, hphi, ht34, u4elo3]
                · linarith only [h0, h1103, h1108, h1180, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
              · linarith only [h0, h1103, h1105, h1109, h1179, hc13, hlam, hphi, ht34, u4elo3]
          · linarith only [h0, h1103, h1104, h1108, hc12, hlam, hphi, ht23, ht34, u4elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1218 | h1218
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1219 | h1219
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1220 | h1220
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1221 | h1221
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1222 | h1222
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1223 | h1223
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1224 | h1224
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1225 | h1225
                        · rcases h5bigk with h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c | h1226c
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [hlam, p1226_0]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h0, h1103, h1218, h1223, h1225, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1226_1, u4elo1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h0, h1103, h1223, h1225, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1226_1, u4elo1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h0, h1103, h1225, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1226_1, u4elo1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h0, h1103, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1226_1, u4elo1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1103, hlam, p1226_0]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [hlam, p1226_0]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h0, h1103, h1223, h1225, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1226_1, u4elo1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h0, h1103, h1225, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1226_1, u4elo1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h0, h1103, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1226_1, u4elo1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1104, hlam, p1226_1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1218, hlam, p1226_1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [hlam, p1226_0]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1218, h1225, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1226_1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h0, h1103, h1218, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1226_1, u4elo1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1105, hlam, p1226_1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1220, hlam, p1226_1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1223, hlam, p1226_0]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [hlam, p1226_0]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1105, hc03, hc45, hlam, hphi, ht0b, ht5b, p1226_1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1106, hlam, p1226_1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1221, hlam, p1226_1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1224, hlam, p1226_1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [h1225, hlam, p1226_1]
                          · have p1226_0 := h1226c.1
                            have p1226_1 := h1226c.2.1
                            have p1226_2 := h1226c.2.2.1
                            have p1226_3 := h1226c.2.2.2
                            linarith only [hlam, p1226_0]
                        · linarith only [h0, h1106, h1225, hc34, hlam, hphi, u4elo1]
                      · linarith only [h0, h1103, h1221, h1222, h1224, hc34, hlam, hphi, u4elo1]
                    · linarith only [h0, h1103, h1105, h1107, h1219, h1223, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h1107, h1219, h1222, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h0, h1103, h1218, h1221, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
              · linarith only [h0, h1103, h1105, h1218, h1219, h1220, hc03, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1258 | h1258
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1259 | h1259
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1260 | h1260
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1261 | h1261
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1262 | h1262
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1263 | h1263
                        · rcases h5bigk with h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h0, h1103, h1218, h1261, h1263, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h0, h1103, h1261, h1263, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1264_1, u4elo1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h0, h1103, h1263, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1264_1, u4elo1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h0, h1103, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1264_1, u4elo1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1103, hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h0, h1103, h1261, h1263, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1264_1, u4elo1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h0, h1103, h1219, h1260, h1263, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1264_1, u4elo2]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h0, h1103, h1219, h1260, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1264_1, u4elo2]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1104, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1218, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1104, h1263, hc02, hc45, hlam, hphi, ht0b, ht5b, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h0, h1103, h1218, h1219, h1260, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1264_1, u4elo2]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1105, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1258, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1261, hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hlam, p1264_0]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1105, hc03, hc45, hlam, hphi, ht0b, ht5b, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1106, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1259, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1262, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [h1263, hlam, p1264_1]
                          · have p1264_0 := h1264c.1
                            have p1264_1 := h1264c.2.1
                            have p1264_2 := h1264c.2.2.1
                            have p1264_3 := h1264c.2.2.2
                            linarith only [hlam, p1264_0]
                        · linarith only [h0, h1219, h1263, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h0, h1103, h1219, h1259, h1260, h1262, hlam]
                    · linarith only [h0, h1103, h1218, h1219, h1260, h1261, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h1107, h1260, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h0, h1103, h1218, h1259, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
              · linarith only [h0, h1103, h1105, h1258, hc13, hlam, hphi, ht34, u4elo1]
          · linarith only [h0, h1103, h1104, h1218, hc12, hlam, hphi, ht23, ht34, u4elo1]
      · linarith only [h0, h1103, h1106, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1298 | h1298
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1299 | h1299
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1300 | h1300
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1301 | h1301
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1302 | h1302
              · linarith only [h0, h1103, h1105, h1302, hc03, hlam, hphi, ht34, u4elo1]
              · linarith only [h0, h1103, h1302, hc13, hlam, hphi, ht34, u4elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1305 | h1305
              · linarith only [h1105, h1301, h1305, hc03, hlam, hphi, ht34, u4elo3]
              · linarith only [h0, h1103, h1301, h1305, hc13, hlam, hphi, ht34, u4elo3]
          · linarith only [h0, h1103, h1104, h1300, hc12, hlam, hphi, ht23, ht34, u4elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1309 | h1309
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1310 | h1310
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1311 | h1311
              · linarith only [h0, h1103, h1105, h1311, hc03, hlam, hphi, ht34, u4elo1]
              · linarith only [h0, h1103, h1311, hc13, hlam, hphi, ht34, u4elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1314 | h1314
              · linarith only [h1105, h1310, h1314, hc03, hlam, hphi, ht34, u4elo3]
              · linarith only [h0, h1103, h1310, h1314, hc13, hlam, hphi, ht34, u4elo3]
          · linarith only [h0, h1103, h1104, h1309, hc12, hlam, hphi, ht23, ht34, u4elo1]
      · linarith only [h0, h1103, h1298, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1319 | h1319
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1320 | h1320
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1321 | h1321
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1322 | h1322
          · linarith only [h0, h1103, h1104, h1322, hc02, hlam, hphi, ht23, ht34, u4elo0]
          · linarith only [h0, h1103, h1322, hc12, hlam, hphi, ht23, ht34, u4elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1325 | h1325
          · linarith only [h1104, h1321, h1325, hc02, hc23, hlam, hphi]
          · linarith only [h0, h1103, h1325, hc12, hlam, hphi, ht23, ht34, u4elo1]
      · linarith only [h0, h1103, h1320, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1329 | h1329
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1330 | h1330
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1331 | h1331
          · linarith only [h0, h1103, h1104, h1331, hc02, hlam, hphi, ht23, ht34, u4elo0]
          · linarith only [h0, h1103, h1331, hc12, hlam, hphi, ht23, ht34, u4elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1334 | h1334
          · linarith only [h1104, h1330, h1334, hc02, hc23, hlam, hphi]
          · linarith only [h0, h1103, h1334, hc12, hlam, hphi, ht23, ht34, u4elo1]
      · linarith only [h0, h1103, h1329, hlam]

end R2N4
