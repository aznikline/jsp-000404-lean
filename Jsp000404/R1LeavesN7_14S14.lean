import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S11
import Jsp000404.R1LeavesN7_14S12
import Jsp000404.R1LeavesN7_14S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h10831 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h11080 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 3 5 (by decide) (by decide) with h11714 | h11714
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11715 | h11715
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11716 | h11716
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11717 | h11717
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11718 | h11718
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11719 | h11719
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11720 | h11720
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11721 | h11721
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11722 | h11722
                  · linarith only [h11080, h11714, h11716, h11722, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h11716, h11719, h11722, h8056, hc01, hc12, hlam, hphi]
                · linarith only [h10831, h11715, h11718, h11721, h6681, hc01, hc12, hlam, hphi]
              · linarith only [h11080, h11719, h11720, hc03, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11727 | h11727
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11728 | h11728
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11729 | h11729
                  · linarith only [h11716, h11719, h11729, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11731 | h11731
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11732 | h11732
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11733 | h11733
                        · rcases h0bigk with h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c | h11734c
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [hlam, p11734_0]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h0, hlam, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h4610, hlam, p11734_0]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h6681, hlam, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h7494, hlam, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h10831, h11718, hc01, hc15, hlam, hphi, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [hlam, p11734_0]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h8056, hlam, p11734_0]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h10364, hlam, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h10831, hlam, p11734_0]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h11719, h4610, hc01, hc34, hlam, hphi, ht12, ht23, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h11719, h4610, hc02, hc34, hlam, hphi, ht23, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [hlam, p11734_0]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h11080, hlam, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h11719, h4610, h7494, hc01, hc34, hlam, hphi, ht12, ht23, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h10364, h11717, hc01, hc12, hlam, hphi, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h0, h10364, h11717, hc01, hc12, hlam, hphi, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h10364, h11714, h11717, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [hlam, p11734_0]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h0, h10364, h10831, h11717, hc01, hc12, hlam, hphi, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h11714, h11719, h4610, hc01, hc34, hlam, hphi, ht12, ht23, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h0, h11714, h11716, h11719, h8056, hc01, hc34, hlam, hphi, ht12, ht23, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h11714, hlam, p11734_0]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [h11715, hlam, p11734_1]
                          · have p11734_0 := h11734c.1
                            have p11734_1 := h11734c.2.1
                            have p11734_2 := h11734c.2.2.1
                            have p11734_3 := h11734c.2.2.2
                            linarith only [hlam, p11734_0]
                        · linarith only [h11719, h11733, h4610, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h10364, h11715, h11732, hlam]
                    · linarith only [h11714, h11731, h8056, hlam]
                · linarith only [h10364, h11715, h11717, h11728, hlam]
              · linarith only [h11714, h11716, h11727, h8056, hlam]
          · linarith only [h0, h10364, h11717, h11718, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11716, h11717, h8056, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11767 | h11767
        · linarith only [h0, h10364, h11716, h11767, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11769 | h11769
          · linarith only [h0, h10831, h11716, h11769, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11771 | h11771
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11772 | h11772
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11773 | h11773
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11774 | h11774
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11775 | h11775
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11776 | h11776
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11777 | h11777
                        · rcases h0bigk with h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c | h11778c
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [hlam, p11778_0]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h0, hlam, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h4610, hlam, p11778_0]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h6681, hlam, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h7494, hlam, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h0, h11769, h11774, h11776, hc01, hc23, hlam, hphi, ht12, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [hlam, p11778_0]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h8056, hlam, p11778_0]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h10364, hlam, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h10831, hlam, p11778_0]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h11080, hc01, hc34, hlam, hphi, ht12, ht23, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h0, h11080, hc01, hc34, hlam, hphi, ht12, ht23, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [hlam, p11778_0]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h11080, hlam, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h0, h10831, h11080, hc01, hc34, hlam, hphi, ht12, ht23, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h11080, h11716, h11771, hc01, hc23, hlam, hphi, ht12, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h0, h11080, h11716, h11771, hc01, hc23, hlam, hphi, ht12, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h11080, h11714, h11716, h11771, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [hlam, p11778_0]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h0, h10831, h11080, h11716, h11771, hc01, hc23, hlam, hphi, ht12, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h11080, h11714, h11716, h11771, hc01, hc23, hlam, hphi, ht12, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h0, h11080, h11714, h11716, h11771, hc01, hc23, hlam, hphi, ht12, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h11714, hlam, p11778_0]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [h11715, hlam, p11778_1]
                          · have p11778_0 := h11778c.1
                            have p11778_1 := h11778c.2.1
                            have p11778_2 := h11778c.2.2.1
                            have p11778_3 := h11778c.2.2.2
                            linarith only [hlam, p11778_0]
                        · linarith only [h11080, h11715, h11777, hlam]
                      · linarith only [h0, h10364, h11080, h11714, h11715, h11771, h11776, hc01, hc14, hlam, hphi]
                    · linarith only [h11080, h11716, h11771, h11775, hc03, hc35, hlam, hphi]
                  · linarith only [h11716, h11771, h11774, hlam]
                · linarith only [h11080, h11714, h11715, h11771, h11773, h6681, hc01, hc13, hlam, hphi]
              · linarith only [h11080, h11714, h11771, h11772, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11810 | h11810
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11811 | h11811
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11812 | h11812
                  · linarith only [h0, h11769, h11771, h11810, h11812, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11716, h11812, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11715, h11811, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h11714, h11810, h4610, hlam]
    · linarith only [h11080, h11714, h11715, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11818 | h11818
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11819 | h11819
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11820 | h11820
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11821 | h11821
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11822 | h11822
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11823 | h11823
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11824 | h11824
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11825 | h11825
                  · linarith only [h0, h11080, h11819, h11825, h8056, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11822, h11825, h8056, hc01, hc13, hlam, hphi]
                · linarith only [h11818, h11824, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h0, h11080, h11822, h11823, h8056, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11830 | h11830
              · linarith only [h0, h11714, h11822, h11830, h8056, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11832 | h11832
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11833 | h11833
                  · linarith only [h11822, h11833, h4610, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11835 | h11835
                    · linarith only [h11819, h11830, h11835, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11837 | h11837
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11838 | h11838
                        · rcases h0bigk with h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c | h11839c
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [hlam, p11839_0]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h0, hlam, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h4610, hlam, p11839_0]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h6681, hlam, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h7494, hlam, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h11819, h8056, hc01, hc13, hlam, hphi, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [hlam, p11839_0]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h8056, hlam, p11839_0]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h10364, hlam, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h10831, hlam, p11839_0]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h11830, h11838, h4610, hc01, hc34, hlam, hphi, ht12, ht23, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h11819, h11830, h11838, h8056, hc02, hc34, hlam, hphi, ht23, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [hlam, p11839_0]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h11080, hlam, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h11714, hlam, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h10364, h11820, hc01, hc12, hlam, hphi, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h0, h10364, h11820, hc01, hc12, hlam, hphi, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h10364, h11820, h4610, hc01, hc12, hlam, hphi, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [hlam, p11839_0]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h0, h10364, h11714, h11820, h8056, hc01, hc12, hlam, hphi, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h10364, h11818, h11820, hc01, hc12, hlam, hphi, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h0, h10364, h11818, h11820, hc01, hc12, hlam, hphi, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h0, h10364, h11818, h11820, h8056, hc01, hc12, hlam, hphi, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [h11818, hlam, p11839_1]
                          · have p11839_0 := h11839c.1
                            have p11839_1 := h11839c.2.1
                            have p11839_2 := h11839c.2.2.1
                            have p11839_3 := h11839c.2.2.2
                            linarith only [hlam, p11839_0]
                        · linarith only [h0, h10364, h11080, h11818, h11820, h11838, h8056, hc01, hc12, hlam, hphi]
                      · linarith only [h10364, h11818, h11837, hlam]
                · linarith only [h10364, h11818, h11820, h11832, hlam]
          · linarith only [h0, h10364, h11820, h11821, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11819, h11820, h8056, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11870 | h11870
        · linarith only [h0, h10364, h11819, h11870, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11872 | h11872
          · linarith only [h0, h10831, h11819, h11872, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11874 | h11874
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11875 | h11875
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11876 | h11876
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11877 | h11877
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11878 | h11878
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11879 | h11879
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11880 | h11880
                        · rcases h0bigk with h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c | h11881c
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [hlam, p11881_0]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h0, hlam, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h4610, hlam, p11881_0]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h6681, hlam, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h7494, hlam, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h11714, h11874, h11880, h8056, hc01, hc13, hlam, hphi, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [hlam, p11881_0]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h8056, hlam, p11881_0]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h10364, hlam, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h10831, hlam, p11881_0]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h11714, h11874, h11880, hc01, hc13, hlam, hphi, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h11714, h11874, h11880, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [hlam, p11881_0]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h11080, hlam, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h11714, hlam, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h11080, h11874, hc01, hc13, hlam, hphi, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h0, h11080, h11874, hc01, hc13, hlam, hphi, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h11080, h11874, h4610, hc01, hc13, hlam, hphi, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [hlam, p11881_0]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h0, h11080, h11714, h11874, h8056, hc01, hc13, hlam, hphi, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h11714, h11874, h11880, hc01, hc13, hlam, hphi, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h0, h11714, h11874, h11880, hc01, hc13, hlam, hphi, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h0, h11714, h11874, h11880, h8056, hc01, hc13, hlam, hphi, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [h11818, hlam, p11881_1]
                          · have p11881_0 := h11881c.1
                            have p11881_1 := h11881c.2.1
                            have p11881_2 := h11881c.2.2.1
                            have p11881_3 := h11881c.2.2.2
                            linarith only [hlam, p11881_0]
                        · linarith only [h11080, h11818, h11880, hlam]
                      · linarith only [h0, h10364, h11818, h11879, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h11080, h11819, h11874, h11878, h8056, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h11819, h11874, h11877, hlam]
                · linarith only [h11080, h11818, h11874, h11876, hlam]
              · linarith only [h0, h11080, h11874, h11875, h8056, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11913 | h11913
              · linarith only [h0, h11714, h11874, h11913, h8056, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11915 | h11915
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11916 | h11916
                  · linarith only [h11874, h11916, h4610, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11819, h11916, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11818, h11915, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11920 | h11920
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11921 | h11921
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11922 | h11922
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11923 | h11923
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11924 | h11924
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11925 | h11925
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11926 | h11926
                  · linarith only [h0, h11080, h11920, h11926, h8056, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11920, h11923, h11926, h8056, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11929 | h11929
                  · linarith only [h0, h11080, h11920, h11929, h8056, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11923, h11925, h11929, h8056, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h11080, h11923, h11924, h8056, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11933 | h11933
              · linarith only [h0, h11714, h11923, h11933, h8056, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11935 | h11935
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11936 | h11936
                  · linarith only [h11923, h11936, h4610, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11938 | h11938
                    · linarith only [h11920, h11933, h11938, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11940 | h11940
                      · linarith only [h0, h11080, h11818, h11921, h11940, h8056, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h10364, h11935, h11940, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11943 | h11943
                  · linarith only [h0, h11080, h11920, h11943, h8056, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11945 | h11945
                    · linarith only [h0, h11714, h11920, h11945, h8056, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11947 | h11947
                      · linarith only [h11921, h11935, h11947, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11949 | h11949
                        · linarith only [h11923, h11935, h11949, h4610, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h11920, h11923, h11949, h8056, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h11920, h11922, h8056, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11920, h11921, h8056, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11954 | h11954
        · linarith only [h0, h10364, h11920, h11954, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11956 | h11956
          · linarith only [h0, h10831, h11920, h11956, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11958 | h11958
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11959 | h11959
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11960 | h11960
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11961 | h11961
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11962 | h11962
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11963 | h11963
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11964 | h11964
                        · linarith only [h0, h11080, h11818, h11958, h11964, h8056, hc01, hc13, hlam, hphi]
                        · linarith only [h0, h11080, h11960, h11964, h8056, hc01, hc14, hlam, hphi]
                      · linarith only [h11954, h11960, h11963, hlam]
                    · linarith only [h11920, h11959, h11962, hlam]
                  · linarith only [h0, h11714, h11920, h11959, h11961, h8056, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11970 | h11970
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11971 | h11971
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11972 | h11972
                      · linarith only [h11960, h11972, h6681, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h11954, h11972, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h11920, h11959, h11971, hlam]
                  · linarith only [h0, h11714, h11920, h11958, h11959, h11970, h8056, hc01, hc14, hlam, hphi]
              · linarith only [h0, h11080, h11958, h11959, h8056, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11978 | h11978
              · linarith only [h0, h11714, h11958, h11978, h8056, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11980 | h11980
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11981 | h11981
                  · linarith only [h11958, h11981, h4610, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11920, h11981, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11984 | h11984
                  · linarith only [h0, h11920, h11958, h11984, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11920, h11984, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h10831 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 3 4 (by decide) (by decide) with h11080 | h11080
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h10364 h10831 h11080
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h10364 h10831 h11080

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 2 5 (by decide) (by decide) with h10831 | h10831
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h10364 h10831
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h10364 h10831

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 2 4 (by decide) (by decide) with h10364 | h10364
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h10364
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h10364

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 2 3 (by decide) (by decide) with h8056 | h8056
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056

end R2N4
