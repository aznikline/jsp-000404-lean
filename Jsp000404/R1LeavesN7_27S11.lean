import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h5 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 1 2 4 (by decide) (by decide) with h664 | h664
  · rcases m.htr 1 2 5 (by decide) (by decide) with h665 | h665
    · rcases m.htr 1 3 4 (by decide) (by decide) with h666 | h666
      · rcases m.htr 1 3 5 (by decide) (by decide) with h667 | h667
        · rcases m.htr 1 4 5 (by decide) (by decide) with h668 | h668
          · linarith only [h0, h5, h668, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h670 | h670
            · rcases m.htr 2 3 5 (by decide) (by decide) with h671 | h671
              · rcases m.htr 2 4 5 (by decide) (by decide) with h672 | h672
                · linarith only [h0, h5, h664, h672, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h674 | h674
                  · linarith only [h5, h666, h674, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases h5bigk with h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p676_1, u1elo0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h1, h670, h672, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p676_1, u1elo0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h1, h674, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p676_1, u1elo0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h5, hlam, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h1, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h670, h672, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p676_1, u1elo4]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h674, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p676_1, u1elo4]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h668, hlam, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h3, hlam, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h665, hlam, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h3, h674, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h672, hlam, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h4, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h667, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h671, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h674, hlam, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h4, h674, hc34, hc45, hlam, hphi, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h667, h674, hc34, hc45, hlam, hphi, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h671, h674, hc34, hc45, hlam, hphi, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h674, hc34, hc45, hlam, hphi, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hlam, p676_0]
              · linarith only [h1, h667, h670, h671, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h703 | h703
              · linarith only [h0, h666, h670, h703, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h705 | h705
                · linarith only [h0, h2, h5, h666, h670, h705, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h707 | h707
                  · linarith only [h0, h5, h666, h707, hlam]
                  · rcases h5bigk with h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [hlam, p709_0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h666, h668, h670, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h1, h705, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p709_1, u1elo0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h1, h703, h705, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p709_1, u1elo0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h5, hlam, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h1, hlam, p709_0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [hlam, p709_0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h1, h705, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p709_1, u1elo0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h1, h703, h705, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p709_1, u1elo0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h668, hlam, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h3, hlam, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h665, hlam, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [hlam, p709_0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h703, hlam, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h705, hlam, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h4, hlam, p709_0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h667, hlam, p709_0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h4, h705, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [hlam, p709_0]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h707, hlam, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h1, h666, h668, h670, hc23, hc45, hlam, hphi, ht34, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h666, h668, h670, hc23, hc45, hlam, hphi, ht34, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h670, h705, hc23, hc45, hlam, hphi, ht34, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [h703, hc23, hc45, hlam, hphi, ht34, p709_1]
                    · have p709_0 := h709c.1
                      have p709_1 := h709c.2.1
                      have p709_2 := h709c.2.2.1
                      have p709_3 := h709c.2.2.2
                      linarith only [hlam, p709_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h735 | h735
          · linarith only [h0, h5, h735, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h737 | h737
            · rcases m.htr 2 3 5 (by decide) (by decide) with h738 | h738
              · linarith only [h665, h666, h667, h738, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h740 | h740
                · linarith only [h2, h4, h5, h666, h667, h740, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h742 | h742
                  · linarith only [h1, h4, h5, h666, h667, h742, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h5bigk with h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [hlam, p744_0]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p744_1, u1elo0]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht5b, p744_1, u1elo0]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h1, h667, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p744_1, u1elo0]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h5, hlam, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h1, hlam, p744_0]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [hlam, p744_0]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p744_1, u1elo4]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h667, hlam, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h735, hlam, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h3, hlam, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h665, hlam, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [hlam, p744_0]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h738, hlam, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h740, hlam, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h4, hlam, p744_0]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h4, hc03, hc15, hlam, hphi, ht0b, ht5b, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h1, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, p744_1, u1elo0]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [hlam, p744_0]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h742, hlam, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h4, h738, hc23, hc45, hlam, hphi, ht34, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h666, h667, hc34, hc45, hlam, hphi, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h737, h738, hc34, hc45, hlam, hphi, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [h666, h667, hc34, hc45, hlam, hphi, p744_1]
                    · have p744_0 := h744c.1
                      have p744_1 := h744c.2.1
                      have p744_2 := h744c.2.2.1
                      have p744_3 := h744c.2.2.2
                      linarith only [hlam, p744_0]
            · linarith only [h666, h667, h737, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h771 | h771
        · rcases m.htr 1 4 5 (by decide) (by decide) with h772 | h772
          · linarith only [h0, h5, h772, hlam]
          · linarith only [h666, h771, h772, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h775 | h775
          · linarith only [h0, h4, h5, h771, h775, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h777 | h777
            · linarith only [h664, h666, h777, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h779 | h779
              · linarith only [h771, h777, h779, hc13, hc34, hlam, hphi]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h781 | h781
                · linarith only [h0, h5, h664, h781, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h783 | h783
                  · linarith only [h4, h5, h783, hlam]
                  · rcases h5bigk with h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [hlam, p785_0]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h1, h664, h775, h777, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p785_1, u1elo0]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h1, h777, h781, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p785_1, u1elo0]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p785_1, u1elo0]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h5, hlam, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h1, hlam, p785_0]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [hlam, p785_0]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h777, h781, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p785_1, u1elo4]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h771, hlam, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h775, hlam, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h3, hlam, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h665, hlam, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [hlam, p785_0]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h779, hlam, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h781, hlam, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h4, hlam, p785_0]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h4, hc03, hc15, hlam, hphi, ht0b, ht5b, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h1, h4, h777, h781, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p785_1, u1elo0]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [hlam, p785_0]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h783, hlam, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h1, h665, h777, h781, hc23, hc45, hlam, hphi, ht34, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h665, h777, h781, hc23, hc45, hlam, hphi, ht34, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h777, h781, hc23, hc45, hlam, hphi, ht34, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [h771, hc13, hc45, hlam, hphi, ht34, p785_1]
                    · have p785_0 := h785c.1
                      have p785_1 := h785c.2.1
                      have p785_2 := h785c.2.2.1
                      have p785_3 := h785c.2.2.2
                      linarith only [hlam, p785_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h811 | h811
      · rcases m.htr 1 3 5 (by decide) (by decide) with h812 | h812
        · rcases m.htr 1 4 5 (by decide) (by decide) with h813 | h813
          · linarith only [h0, h5, h813, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h815 | h815
            · rcases m.htr 2 3 5 (by decide) (by decide) with h816 | h816
              · rcases m.htr 2 4 5 (by decide) (by decide) with h817 | h817
                · linarith only [h3, h5, h664, h665, h817, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h819 | h819
                  · linarith only [h3, h5, h664, h665, h815, h819, hlam]
                  · rcases h5bigk with h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [hlam, p821_0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h664, h665, h815, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h1, h664, h665, h815, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p821_1, u1elo0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p821_1, u1elo0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h5, hlam, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h1, hlam, p821_0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [hlam, p821_0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h665, hlam, p821_0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p821_1, u1elo4]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h813, hlam, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h3, hlam, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [hlam, p821_0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h1, h3, hc35, hlam, hphi, ht01, ht0b, ht5b, p821_1, u1elo0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h817, hlam, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h4, hlam, p821_0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h812, hlam, p821_0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h816, hlam, p821_0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [hlam, p821_0]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h819, hlam, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h1, h664, h665, h815, hc34, hc45, hlam, hphi, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h664, h665, h815, hc34, hc45, hlam, hphi, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h664, h665, h815, hc34, hc45, hlam, hphi, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [h819, hc34, hc45, hlam, hphi, p821_1]
                    · have p821_0 := h821c.1
                      have p821_1 := h821c.2.1
                      have p821_2 := h821c.2.2.1
                      have p821_3 := h821c.2.2.2
                      linarith only [hlam, p821_0]
              · linarith only [h812, h815, h816, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h848 | h848
              · linarith only [h0, h811, h815, h848, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h664, h665, h811, h812, h815, h848, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h851 | h851
          · linarith only [h0, h5, h851, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h853 | h853
            · rcases m.htr 2 3 5 (by decide) (by decide) with h854 | h854
              · rcases m.htr 2 4 5 (by decide) (by decide) with h855 | h855
                · linarith only [h3, h5, h664, h812, h854, h855, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h857 | h857
                  · linarith only [h3, h5, h664, h665, h853, h857, hlam]
                  · rcases h5bigk with h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [hlam, p859_0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h664, h665, h853, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h1, h664, h665, h853, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p859_1, u1elo0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h1, h811, h812, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p859_1, u1elo0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h5, hlam, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h1, hlam, p859_0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [hlam, p859_0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h665, hlam, p859_0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h812, hlam, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h851, hlam, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h3, hlam, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h664, h665, h853, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [hlam, p859_0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h1, h3, h811, h812, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p859_1, u1elo0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h855, hlam, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h4, hlam, p859_0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h664, h665, h853, h854, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h854, hlam, p859_0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [hlam, p859_0]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h857, hlam, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h1, h664, h665, h853, hc34, hc45, hlam, hphi, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h664, h665, h853, hc34, hc45, hlam, hphi, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h664, h665, h853, hc34, hc45, hlam, hphi, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [h811, h812, hc34, hc45, hlam, hphi, p859_1]
                    · have p859_0 := h859c.1
                      have p859_1 := h859c.2.1
                      have p859_2 := h859c.2.2.1
                      have p859_3 := h859c.2.2.2
                      linarith only [hlam, p859_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h885 | h885
                · linarith only [h1, h664, h665, h885, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h887 | h887
                  · linarith only [h4, h5, h664, h665, h853, h854, h887, hlam]
                  · rcases h5bigk with h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p889_1, u1elo0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h1, h664, h665, h853, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p889_1, u1elo0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h1, h854, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p889_1, u1elo0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h5, hlam, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h1, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h665, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h812, hlam, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h851, hlam, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h3, hlam, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h854, hlam, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h885, hlam, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h4, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h664, h665, h853, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h1, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, p889_1, u1elo0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h887, hlam, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h1, h664, h665, h853, hc34, hc45, hlam, hphi, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h664, h665, h853, hc34, hc45, hlam, hphi, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h664, h665, h853, hc34, hc45, hlam, hphi, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h664, h665, h853, h854, hc34, hc45, hlam, hphi, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [hlam, p889_0]
            · linarith only [h1, h4, h811, h812, h853, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h916 | h916
        · linarith only [h664, h665, h811, h916, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h918 | h918
          · linarith only [h0, h5, h918, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h920 | h920
            · linarith only [h1, h3, h664, h665, h811, h920, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h922 | h922
              · linarith only [h664, h665, h916, h920, h922, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h924 | h924
                · linarith only [h4, h5, h664, h665, h922, h924, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h926 | h926
                  · linarith only [h4, h5, h664, h665, h920, h922, h926, hc23, hc34, hlam, hphi]
                  · rcases h5bigk with h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [hlam, p928_0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h1, h664, h665, h920, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p928_1, u1elo0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht5b, p928_1, u1elo0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p928_1, u1elo0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h5, hlam, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h1, hlam, p928_0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [hlam, p928_0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h665, hlam, p928_0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h916, hlam, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h918, hlam, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h3, hlam, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h664, h665, h920, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [hlam, p928_0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h922, hlam, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h924, hlam, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h4, hlam, p928_0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h664, h665, h920, hc23, hc35, hlam, hphi, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h1, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, p928_1, u1elo0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [hlam, p928_0]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h926, hlam, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h1, h664, h665, h920, hc23, hc45, hlam, hphi, ht34, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h664, h665, h920, hc23, hc45, hlam, hphi, ht34, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h664, h665, h920, hc23, hc45, hlam, hphi, ht34, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [h664, h665, h920, h922, hc23, hc45, hlam, hphi, ht34, p928_1]
                    · have p928_0 := h928c.1
                      have p928_1 := h928c.2.1
                      have p928_2 := h928c.2.2.1
                      have p928_3 := h928c.2.2.2
                      linarith only [hlam, p928_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h954 | h954
    · rcases m.htr 1 3 4 (by decide) (by decide) with h955 | h955
      · rcases m.htr 1 3 5 (by decide) (by decide) with h956 | h956
        · rcases m.htr 1 4 5 (by decide) (by decide) with h957 | h957
          · linarith only [h2, h5, h664, h954, h957, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
          · linarith only [h664, h954, h957, hlam]
        · linarith only [h2, h5, h664, h954, h955, h956, hc34, hc45, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h961 | h961
        · rcases m.htr 1 4 5 (by decide) (by decide) with h962 | h962
          · linarith only [h2, h5, h664, h954, h962, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
          · linarith only [h664, h954, h962, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h965 | h965
          · linarith only [h2, h5, h664, h954, h965, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
          · linarith only [h664, h954, h965, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h968 | h968
      · rcases m.htr 1 3 5 (by decide) (by decide) with h969 | h969
        · rcases m.htr 1 4 5 (by decide) (by decide) with h970 | h970
          · linarith only [h0, h5, h970, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h972 | h972
            · rcases m.htr 2 3 5 (by decide) (by decide) with h973 | h973
              · rcases m.htr 2 4 5 (by decide) (by decide) with h974 | h974
                · linarith only [h2, h5, h974, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h976 | h976
                  · linarith only [h2, h5, h664, h968, h976, hlam]
                  · rcases h5bigk with h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [hlam, p978_0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h1, h970, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p978_1, u1elo0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h1, h954, h968, h970, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p978_1, u1elo0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p978_1, u1elo0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h5, hlam, p978_1]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h1, hlam, p978_0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [hlam, p978_0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h954, hlam, p978_0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p978_1, u1elo4]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h970, hlam, p978_1]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h3, hlam, p978_1]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p978_1]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [hlam, p978_0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h1, h3, hc35, hlam, hphi, ht01, ht0b, ht5b, p978_1, u1elo0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h974, hlam, p978_1]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h4, hlam, p978_0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h969, hlam, p978_0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h973, hlam, p978_0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [hlam, p978_0]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h976, hlam, p978_1]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h1, h664, h970, hc12, hc45, hlam, hphi, ht23, ht34, p978_1]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h664, h970, hc12, hc45, hlam, hphi, ht23, ht34, p978_1]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h954, hc12, hc45, hlam, hphi, ht23, ht34, p978_1]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [h976, hc34, hc45, hlam, hphi, p978_1]
                    · have p978_0 := h978c.1
                      have p978_1 := h978c.2.1
                      have p978_2 := h978c.2.2.1
                      have p978_3 := h978c.2.2.2
                      linarith only [hlam, p978_0]
              · linarith only [h1, h969, h972, h973, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h664, h968, h972, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1006 | h1006
          · linarith only [h1, h1006, h2, h4, h5, h664, h968, h969, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1008 | h1008
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1009 | h1009
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1010 | h1010
                · linarith only [h0, h1009, h1010, h2, h3, h5, h968, h969, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1012 | h1012
                  · linarith only [h1009, h1012, h3, h5, h968, h969, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h5bigk with h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [hlam, p1014_0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1014_1, u1elo0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht5b, p1014_1, u1elo0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h1, h969, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1014_1, u1elo0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h5, hlam, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h1, hlam, p1014_0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [hlam, p1014_0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h954, hlam, p1014_0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h969, hlam, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h1006, hlam, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h3, hlam, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [hlam, p1014_0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h1, h3, h968, h969, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1014_1, u1elo0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h1010, hlam, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h4, hlam, p1014_0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h968, h969, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h1009, hlam, p1014_0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [hlam, p1014_0]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h1012, hlam, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h1, h968, h969, hc34, hc45, hlam, hphi, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h968, h969, hc34, hc45, hlam, hphi, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h954, hc12, hc45, hlam, hphi, ht23, ht34, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [h968, h969, hc34, hc45, hlam, hphi, p1014_1]
                    · have p1014_0 := h1014c.1
                      have p1014_1 := h1014c.2.1
                      have p1014_2 := h1014c.2.2.1
                      have p1014_3 := h1014c.2.2.2
                      linarith only [hlam, p1014_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1040 | h1040
                · linarith only [h1040, h2, h5, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1042 | h1042
                  · linarith only [h1, h1042, h5, h968, h969, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases h5bigk with h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [hlam, p1044_0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1044_1, u1elo0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht5b, p1044_1, u1elo0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1, h1008, h1009, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1044_1, u1elo0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h5, hlam, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1, hlam, p1044_0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [hlam, p1044_0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h954, hlam, p1044_0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h969, hlam, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1006, hlam, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h3, hlam, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [hlam, p1044_0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1009, hlam, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1040, hlam, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h4, hlam, p1044_0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h954, hc12, hc35, hlam, hphi, ht23, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, p1044_1, u1elo0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [hlam, p1044_0]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1042, hlam, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h4, h969, hc13, hc45, hlam, hphi, ht34, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h968, h969, hc34, hc45, hlam, hphi, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1008, h1009, h664, hc12, hc45, hlam, hphi, ht23, ht34, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [h1008, h1009, h664, hc12, hc45, hlam, hphi, ht23, ht34, p1044_1]
                    · have p1044_0 := h1044c.1
                      have p1044_1 := h1044c.2.1
                      have p1044_2 := h1044c.2.2.1
                      have p1044_3 := h1044c.2.2.2
                      linarith only [hlam, p1044_0]
            · linarith only [h1, h1008, h968, h969, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1071 | h1071
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1072 | h1072
          · linarith only [h1072, h2, h5, h664, hlam]
          · linarith only [h1071, h1072, h968, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1075 | h1075
          · linarith only [h1075, h2, h5, h664, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1077 | h1077
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1078 | h1078
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1079 | h1079
                · linarith only [h1079, h2, h5, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1081 | h1081
                  · linarith only [h1081, h2, h5, h664, hc12, hc34, hlam, hphi, ht23]
                  · rcases h5bigk with h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [hlam, p1083_0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1083_1, u1elo0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1, h1078, hc35, hlam, hphi, ht01, ht0b, ht5b, p1083_1, u1elo0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p1083_1, u1elo0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h5, hlam, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1, hlam, p1083_0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [hlam, p1083_0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h954, hlam, p1083_0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1071, hlam, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1075, hlam, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h3, hlam, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [hlam, p1083_0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1, h1071, h1075, h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1083_1, u1elo0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1079, hlam, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h4, hlam, p1083_0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1075, h4, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1078, hlam, p1083_0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [hlam, p1083_0]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1081, hlam, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1, h1075, hc14, hc45, hlam, hphi, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1075, h664, hc12, hc45, hlam, hphi, ht23, ht34, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h954, hc12, hc45, hlam, hphi, ht23, ht34, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [h1071, hc13, hc45, hlam, hphi, ht34, p1083_1]
                    · have p1083_0 := h1083c.1
                      have p1083_1 := h1083c.2.1
                      have p1083_2 := h1083c.2.2.1
                      have p1083_3 := h1083c.2.2.2
                      linarith only [hlam, p1083_0]
              · linarith only [h1077, h1078, h968, hc13, hc35, hlam, hphi]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1110 | h1110
              · linarith only [h1071, h1077, h1110, hc13, hc34, hlam, hphi]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1112 | h1112
                · linarith only [h1112, h2, h5, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1114 | h1114
                  · linarith only [h1114, h2, h5, h664, hc12, hc34, hlam, hphi, ht23]
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
                      linarith only [h1, h1075, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1116_1, u1elo0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1, h1112, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1116_1, u1elo0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1, h1110, h1112, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1116_1, u1elo0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h5, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1, hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h954, hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1071, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1075, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h3, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1075, h664, hc12, hc25, hlam, hphi, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1110, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1112, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h4, hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1075, h664, hc12, hc35, hlam, hphi, ht23, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, p1116_1, u1elo0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1114, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1, h1075, h664, hc12, hc45, hlam, hphi, ht23, ht34, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1075, h664, hc12, hc45, hlam, hphi, ht23, ht34, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h954, hc12, hc45, hlam, hphi, ht23, ht34, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1110, h1112, h664, hc12, hc45, hlam, hphi, ht23, ht34, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [hlam, p1116_0]

set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_25_L_0_H_I_s1_x0_x0_x0_x0 m hb1 hb5 hg0 hg1 h2 h3 h4 h5
  · exact r1l7_11_25_L_0_H_I_s1_x0_x0_x0_x1 m hb1 hb5 hg0 hg1 h2 h3 h4 h5

end R2N4
