import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_42S12
import Jsp000404.R1LeavesN7_42S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1658 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2081 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2783 | h2783
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2784 | h2784
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2785 | h2785
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2786 | h2786
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2787 | h2787
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2788 | h2788
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2789 | h2789
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2790 | h2790
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2791 | h2791
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2792 | h2792
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2793 | h2793
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2794 | h2794
                        · linarith only [h2081, h2783, h2787, h2794, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2796 | h2796
                          · linarith only [h2792, h2794, h2796, hlam]
                          · rcases h2bigk with h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h0, hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2081, hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2081, h2787, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2798_1]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2081, h2787, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2798_1]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2798_1]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h0, h2081, hc01, hc12, hlam, hphi, p2798_1]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              rcases p2798_3 (m.d 0 2) (by simp) with h2807 | h2807
                              · linarith only [h0, h2807, hlam]
                              · linarith only [h2783, h2807, hlam]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              rcases p2798_3 (m.d 0 2) (by simp) with h2810 | h2810
                              · linarith only [h0, h2810, hlam]
                              · linarith only [h2784, h2810, hlam]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2784, h2787, h2792, h2794, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2798_1]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2787, hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2787, h2792, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2798_1]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2787, h2792, h2794, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2798_1]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2783, hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2788, hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2792, hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2794, hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2784, hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2789, hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2793, hlam, p2798_0]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [h2784, h2792, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2798_1]
                            · have p2798_0 := h2798c.1
                              have p2798_1 := h2798c.2.1
                              have p2798_2 := h2798c.2.2.1
                              have p2798_3 := h2798c.2.2.2
                              linarith only [hlam, p2798_0]
                      · linarith only [h2081, h2793, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h2081, h2785, h2792, hlam]
                  · linarith only [h1658, h2081, h2784, h2786, h2791, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h2081, h2783, h2785, h2787, h2790, hlam]
              · linarith only [h2081, h2787, h2789, hc02, hc25, hlam, hphi]
            · linarith only [h2081, h2783, h2787, h2788, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2834 | h2834
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2835 | h2835
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2836 | h2836
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2837 | h2837
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2838 | h2838
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2839 | h2839
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2840 | h2840
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2841 | h2841
                          · rcases h2bigk with h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h0, hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2081, hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2838, h2841, hc02, hc45, hlam, hphi, ht0b, ht5b, p2842_1]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h0, h2787, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2842_1]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2787, hc02, hc23, hlam, hphi, p2842_1]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2787, hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2787, h2838, h2841, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2842_1]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2787, h2839, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2842_1]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2783, h2838, h2841, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2842_1]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p2842_1]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2838, h2841, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2842_1]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              rcases p2842_3 (m.d 0 2) (by simp) with h2857 | h2857
                              · linarith only [h2081, h2857, hlam]
                              · linarith only [h2784, h2857, hlam]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2783, hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2834, hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2838, hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2783, h2839, h2841, hc02, hc45, hlam, hphi, ht0b, ht5b, p2842_1]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2784, hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2835, hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2839, hlam, p2842_0]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [h2840, hlam, p2842_1]
                            · have p2842_0 := h2842c.1
                              have p2842_1 := h2842c.2.1
                              have p2842_2 := h2842c.2.2.1
                              have p2842_3 := h2842c.2.2.2
                              linarith only [hlam, p2842_0]
                          · linarith only [h0, h2783, h2787, h2840, h2841, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2871 | h2871
                          · linarith only [h2838, h2840, h2871, hlam]
                          · rcases h2bigk with h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h0, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2081, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h0, h2787, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h0, h2787, h2838, h2840, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2787, hc02, hc23, hlam, hphi, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2787, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2787, h2838, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2787, h2838, h2840, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2784, h2838, h2840, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              rcases p2873_3 (m.d 0 2) (by simp) with h2887 | h2887
                              · linarith only [h2081, h2887, hlam]
                              · linarith only [h2783, h2887, hlam]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              rcases p2873_3 (m.d 0 2) (by simp) with h2890 | h2890
                              · linarith only [h2081, h2890, hlam]
                              · linarith only [h2784, h2890, hlam]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2783, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2834, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2838, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2840, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2784, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2835, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2839, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2784, h2838, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hlam, p2873_0]
                      · linarith only [h1658, h2787, h2839, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h2787, h2838, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1658, h2786, h2837, hlam]
                · linarith only [h1658, h2785, h2836, hlam]
              · linarith only [h0, h2784, h2835, hlam]
            · linarith only [h0, h2783, h2834, hlam]
        · linarith only [h2081, h2783, h2786, hc24, hlam, hphi, ht45, u5elo3]
      · linarith only [h2081, h2783, h2785, hlam]
    · linarith only [h2783, h2784, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2912 | h2912
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2913 | h2913
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2914 | h2914
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2915 | h2915
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2916 | h2916
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2917 | h2917
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2918 | h2918
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2919 | h2919
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2920 | h2920
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2921 | h2921
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2922 | h2922
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2923 | h2923
                          · rcases h2bigk with h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h0, hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2081, hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2783, hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2783, h2916, h2921, h2923, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2924_1]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2924_1]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h0, h2081, hc01, hc12, hlam, hphi, p2924_1]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2783, h2912, h2921, h2923, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2924_1]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              rcases p2924_3 (m.d 0 2) (by simp) with h2934 | h2934
                              · linarith only [h0, h2934, hlam]
                              · linarith only [h2912, h2934, hlam]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2912, h2921, h2923, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2924_1]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2915, hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2783, h2912, h2915, h2921, h2923, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2924_1]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2915, h2921, h2923, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2924_1]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2912, h2916, h2921, h2923, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2924_1]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2916, hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2920, hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2915, h2920, h2921, h2923, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2924_1]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2912, hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2917, hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2921, hlam, p2924_0]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [h2922, hlam, p2924_1]
                            · have p2924_0 := h2924c.1
                              have p2924_1 := h2924c.2.1
                              have p2924_2 := h2924c.2.2.1
                              have p2924_3 := h2924c.2.2.2
                              linarith only [hlam, p2924_0]
                          · linarith only [h2081, h2912, h2915, h2922, h2923, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h2783, h2922, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h2081, h2912, h2914, h2921, hc25, hlam, hphi, u5elo0]
                    · linarith only [h2081, h2912, h2913, h2920, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1658, h2783, h2912, h2914, h2919, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h2081, h2913, h2915, h2918, hlam]
              · linarith only [h2081, h2915, h2917, hc02, hc25, hlam, hphi]
            · linarith only [h2081, h2912, h2915, h2916, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2960 | h2960
            · linarith only [h2783, h2915, h2960, hc02, hc23, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2962 | h2962
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2963 | h2963
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2964 | h2964
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2965 | h2965
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2966 | h2966
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2967 | h2967
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2968 | h2968
                          · rcases h2bigk with h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h0, hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2081, hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2783, hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h0, h2960, h2965, h2966, h2968, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2969_1]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2960, h2965, hc02, hc23, hlam, hphi, p2969_1]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2915, hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2960, hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2960, h2965, h2966, h2968, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2969_1]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2912, h2966, h2968, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2969_1]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p2969_1]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2783, h2912, h2966, h2968, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2969_1]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              rcases p2969_3 (m.d 0 2) (by simp) with h2984 | h2984
                              · linarith only [h2081, h2984, hlam]
                              · linarith only [h2912, h2984, hlam]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2912, h2966, h2968, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2969_1]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p2969_1]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2965, hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              rcases p2969_3 (m.d 0 2) (by simp) with h2991 | h2991
                              · linarith only [h2783, h2991, hlam]
                              · linarith only [h2912, h2991, hlam]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2912, hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2962, hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2966, hlam, p2969_0]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [h2967, hlam, p2969_1]
                            · have p2969_0 := h2969c.1
                              have p2969_1 := h2969c.2.1
                              have p2969_2 := h2969c.2.2.1
                              have p2969_3 := h2969c.2.2.2
                              linarith only [hlam, p2969_0]
                          · rcases h2bigk with h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h0, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2081, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2783, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2081, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h0, h2960, hc01, hc14, hlam, hphi, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2915, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2960, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2960, h2965, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2912, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2783, h2912, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2967, h2968, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2912, h2967, h2968, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h0, h2912, h2967, h2968, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2965, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2965, h2967, h2968, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2912, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2962, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2966, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2967, hlam, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [hlam, p2999_0]
                        · linarith only [h2783, h2967, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h1658, h2915, h2966, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h2915, h2965, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2960, h2963, h2964, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h1658, h2913, h2963, hlam]
              · linarith only [h0, h2962, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h2913, h2914, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3032 | h3032
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3033 | h3033
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3034 | h3034
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3035 | h3035
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3036 | h3036
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3037 | h3037
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3038 | h3038
                    · linarith only [h2081, h2912, h2913, h3033, h3038, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h2081, h2912, h3033, h3036, h3038, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h3036, h3037, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3042 | h3042
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3043 | h3043
                    · linarith only [h3033, h3036, h3043, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3045 | h3045
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3046 | h3046
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3047 | h3047
                          · rcases h2bigk with h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h0, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2081, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2783, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2081, h3033, h3036, h3045, h3047, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h1658, h2081, hc01, hc12, hlam, hphi, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2783, h2912, h3045, h3047, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              rcases p3048_3 (m.d 0 2) (by simp) with h3058 | h3058
                              · linarith only [h0, h3058, hlam]
                              · linarith only [h2912, h3058, hlam]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2912, h3045, h3047, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h3033, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h3043, hlam, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h3033, h3036, h3045, h3047, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2912, h3034, h3045, h3047, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h3034, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h3034, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h3034, h3045, h3047, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2912, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h3035, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h3045, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h3046, hlam, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [hlam, p3048_0]
                          · linarith only [h2081, h2912, h3033, h3036, h3045, h3047, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h2783, h2912, h3045, h3046, hc35, hlam, hphi, u5elo4]
                      · linarith only [h2081, h2912, h3045, hc25, hlam, hphi, u5elo3]
                  · linarith only [h2081, h2912, h3032, h3033, h3042, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h3035, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h2081, h3033, h3034, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3082 | h3082
            · linarith only [h2783, h2912, h3033, h3082, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3084 | h3084
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3085 | h3085
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3086 | h3086
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3087 | h3087
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3088 | h3088
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3089 | h3089
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3090 | h3090
                          · rcases h2bigk with h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h0, hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h2081, hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h2783, hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h0, h3082, h3087, h3088, h3090, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3091_1]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h3082, h3087, hc02, hc23, hlam, hphi, p3091_1]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h3033, hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h3082, hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h3082, h3087, h3088, h3090, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3091_1]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h2912, h3088, h3090, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3091_1]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p3091_1]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h2783, h2912, h3088, h3090, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3091_1]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              rcases p3091_3 (m.d 0 2) (by simp) with h3106 | h3106
                              · linarith only [h2081, h3106, hlam]
                              · linarith only [h2912, h3106, hlam]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h2912, h3088, h3090, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3091_1]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3091_1]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h3087, hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              rcases p3091_3 (m.d 0 2) (by simp) with h3113 | h3113
                              · linarith only [h2783, h3113, hlam]
                              · linarith only [h2912, h3113, hlam]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h2912, hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h3084, hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h3088, hlam, p3091_0]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [h3089, hlam, p3091_1]
                            · have p3091_0 := h3091c.1
                              have p3091_1 := h3091c.2.1
                              have p3091_2 := h3091c.2.2.1
                              have p3091_3 := h3091c.2.2.2
                              linarith only [hlam, p3091_0]
                          · linarith only [h2913, h3090, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h2783, h3089, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h2081, h2912, h2913, h3033, h3085, h3088, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h3033, h3085, h3087, hlam]
                  · linarith only [h2913, h3032, h3085, h3086, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3126 | h3126
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3127 | h3127
                    · linarith only [h1658, h3085, h3127, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h3033, h3127, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h3033, h3126, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h3084, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h2081, h2912, h3032, hc25, hlam, hphi, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3133 | h3133
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3134 | h3134
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3135 | h3135
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3136 | h3136
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3137 | h3137
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3138 | h3138
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3139 | h3139
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3140 | h3140
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3141 | h3141
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3142 | h3142
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3143 | h3143
                          · rcases h2bigk with h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h2081, hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h2783, hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h2912, hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p3144_1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, h2081, hc01, hc12, hlam, hphi, p3144_1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, h2783, hc01, hc12, hlam, hphi, p3144_1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, h2912, hc01, hc12, hlam, hphi, p3144_1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3144_1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h3135, hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, h2783, h3135, hc01, hc12, hlam, hphi, p3144_1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, h2912, h3135, hc01, hc12, hlam, hphi, p3144_1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3144_1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h3136, hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h3140, hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, h2912, h3135, h3140, hc01, hc12, hlam, hphi, p3144_1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h0, h3137, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3144_1, u5elo1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h3137, hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h3141, hlam, p3144_0]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [h3142, hlam, p3144_1]
                            · have p3144_0 := h3144c.1
                              have p3144_1 := h3144c.2.1
                              have p3144_2 := h3144c.2.2.1
                              have p3144_3 := h3144c.2.2.2
                              linarith only [hlam, p3144_0]
                          · rcases h2bigk with h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h0, hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h2081, hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h2783, hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h2912, hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p3170_1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h3140, h3142, h3143, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3170_1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h0, h2912, h3137, h3142, h3143, hc01, hc12, hc34, hlam, hphi, ht45, p3170_1, u5elo1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h0, h2912, hc01, hc12, hlam, hphi, p3170_1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3170_1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h3135, hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h0, h2912, h3135, h3137, h3142, h3143, hc01, hc12, hc34, hlam, hphi, ht45, p3170_1, u5elo1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h0, h2912, h3135, hc01, hc12, hlam, hphi, p3170_1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h0, h3136, hc01, hc14, hlam, hphi, p3170_1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h3136, hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h3140, hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h0, h2912, h3135, h3140, hc01, hc12, hlam, hphi, p3170_1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h0, h3137, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3170_1, u5elo1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h3137, hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h3141, hlam, p3170_0]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [h3142, hlam, p3170_1]
                            · have p3170_0 := h3170c.1
                              have p3170_1 := h3170c.2.1
                              have p3170_2 := h3170c.2.2.1
                              have p3170_3 := h3170c.2.2.2
                              linarith only [hlam, p3170_0]
                        · linarith only [h0, h2783, h3142, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h2081, h3141, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h2081, h3133, h3140, hlam]
                  · linarith only [h1658, h2081, h3134, h3139, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h2081, h3133, h3135, h3138, hlam]
              · linarith only [h2081, h3135, h3137, hc03, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h0, h2081, h3135, h3136, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3203 | h3203
            · linarith only [h0, h2783, h3135, h3203, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3205 | h3205
              · linarith only [h0, h2912, h3135, h3205, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3205, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h3133, h3134, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3209 | h3209
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3210 | h3210
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3211 | h3211
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3212 | h3212
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3213 | h3213
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3214 | h3214
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3215 | h3215
                    · linarith only [h3133, h3209, h3210, h3215, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h2081, h3213, h3215, hc01, hc13, hlam, hphi]
                  · linarith only [h3213, h3214, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3219 | h3219
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3220 | h3220
                    · linarith only [h3210, h3213, h3220, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3222 | h3222
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3223 | h3223
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3224 | h3224
                          · rcases h2bigk with h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h0, hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h2081, hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h2783, hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h2912, hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p3225_1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h1658, h2081, hc01, hc12, hlam, hphi, p3225_1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h0, h2783, h2912, h3133, h3209, h3212, hc01, hc12, hc35, hlam, hphi, p3225_1, u5elo1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h0, h2912, hc01, hc12, hlam, hphi, p3225_1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3225_1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h3210, hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h3220, hlam, p3225_1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h0, h2912, h3210, h3213, hc01, hc34, hlam, hphi, ht12, ht23, p3225_1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3225_1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h3211, hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h0, h2912, h3211, h3212, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p3225_1, u5elo1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h0, h2912, h3211, hc01, hc12, hlam, hphi, p3225_1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h0, h3212, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3225_1, u5elo1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h3212, hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h3222, hlam, p3225_0]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [h3223, hlam, p3225_1]
                            · have p3225_0 := h3225c.1
                              have p3225_1 := h3225c.2.1
                              have p3225_2 := h3225c.2.2.1
                              have p3225_3 := h3225c.2.2.2
                              linarith only [hlam, p3225_0]
                          · linarith only [h3213, h3224, hc13, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h2783, h3223, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h2081, h3222, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h2081, h3209, h3210, h3219, hlam]
              · linarith only [h2783, h3211, h3212, hc04, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h2081, h3210, h3211, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3257 | h3257
            · linarith only [h0, h2783, h3210, h3257, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3259 | h3259
              · linarith only [h0, h2912, h3210, h3259, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3259, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3262 | h3262
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3263 | h3263
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3264 | h3264
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3265 | h3265
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3266 | h3266
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3267 | h3267
                    · linarith only [h1658, h3133, h3262, h3267, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h2081, h3265, h3267, hc01, hc13, hlam, hphi]
                  · linarith only [h3265, h3266, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3271 | h3271
                  · linarith only [h0, h2081, h3209, h3265, h3271, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1658, h3271, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h3264, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h2081, h3262, h3263, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3276 | h3276
            · linarith only [h0, h2783, h3262, h3276, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3278 | h3278
              · linarith only [h0, h2912, h3262, h3278, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3278, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1658 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2081 | h2081
  · exact r1l7_22_13_15_H_I_L_I_L_0_x1_x1_x0 m hb2 hb3 hb5 h0 h1658 h2081
  · exact r1l7_22_13_15_H_I_L_I_L_0_x1_x1_x1 m hb2 hb3 hb5 h0 h1658 h2081

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1658 | h1658
  · exact r1l7_22_13_15_H_I_L_I_L_0_x1_x0 m hb2 hb3 hb5 h0 h1658
  · exact r1l7_22_13_15_H_I_L_I_L_0_x1_x1 m hb2 hb3 hb5 h0 h1658

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0 m hb2 hb3 hb5 h0
  · exact r1l7_22_13_15_H_I_L_I_L_0_x1 m hb2 hb3 hb5 h0

end R2N4
