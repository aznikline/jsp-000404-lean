import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2361 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h2582 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h2781 | h2781
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2782 | h2782
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2783 | h2783
      · linarith only [h0, h2, h2783, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2785 | h2785
        · linarith only [h0, h2361, h2785, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2787 | h2787
          · linarith only [h0, h2582, h2787, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2789 | h2789
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2790 | h2790
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2791 | h2791
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2792 | h2792
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2793 | h2793
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2794 | h2794
                      · rcases h2bigk with h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h2582, h2791, h2793, hc12, hc23, hlam, hphi, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h2, hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h2361, hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h2582, hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h0, hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h2783, hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h2785, hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h2787, hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h0, h2361, hc12, hc23, hlam, hphi, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h0, h2582, hc12, hc23, hlam, hphi, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h2791, hlam, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h0, h2582, h2791, hc12, hc23, hlam, hphi, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h2792, hlam, p2795_1]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [h2793, hlam, p2795_0]
                        · have p2795_0 := h2795c.1
                          have p2795_1 := h2795c.2.1
                          have p2795_2 := h2795c.2.2.1
                          have p2795_3 := h2795c.2.2.2
                          linarith only [hlam, p2795_0]
                      · rcases h2bigk with h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h2, hc12, hc23, hlam, hphi, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h2, hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h2361, hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h2582, hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h0, hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h2783, hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h2785, hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h2787, hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h1, h2361, h2790, h2794, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h0, h2582, hc12, hc23, hlam, hphi, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h2791, hlam, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h0, h2582, h2791, hc12, hc23, hlam, hphi, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h2792, hlam, p2821_1]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [h2793, hlam, p2821_0]
                        · have p2821_0 := h2821c.1
                          have p2821_1 := h2821c.2.1
                          have p2821_2 := h2821c.2.2.1
                          have p2821_3 := h2821c.2.2.2
                          linarith only [hlam, p2821_0]
                    · linarith only [h0, h1, h2361, h2790, h2793, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2848 | h2848
                    · linarith only [h2791, h2792, h2848, hlam]
                    · linarith only [h0, h1, h2, h2361, h2781, h2790, h2792, h2848, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h2, h2781, h2791, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2852 | h2852
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2853 | h2853
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2854 | h2854
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2855 | h2855
                      · linarith only [h2789, h2790, h2855, hlam]
                      · rcases h2bigk with h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2, hc12, hc23, hlam, hphi, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2, hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2361, hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2582, hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h0, hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2783, hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2785, hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2787, hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2361, h2782, h2785, h2790, hc12, hc23, hlam, hphi, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2582, h2782, h2785, h2790, hc12, hc23, hlam, hphi, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2852, hlam, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2582, h2782, h2785, h2790, h2852, hc12, hc23, hlam, hphi, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2853, hlam, p2857_1]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [h2854, hlam, p2857_0]
                        · have p2857_0 := h2857c.1
                          have p2857_1 := h2857c.2.1
                          have p2857_2 := h2857c.2.2.1
                          have p2857_3 := h2857c.2.2.2
                          linarith only [hlam, p2857_0]
                    · linarith only [h0, h2, h2361, h2781, h2782, h2854, hc12, hc23, hlam, hphi]
                  · linarith only [h2, h2781, h2782, h2785, h2790, h2853, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h2, h2781, h2782, h2789, h2790, h2852, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2886 | h2886
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2887 | h2887
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2888 | h2888
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2889 | h2889
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2890 | h2890
                      · rcases h2bigk with h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h2, hc12, hc23, hlam, hphi, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h2, hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h2361, hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h2582, hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h0, hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h2783, hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h2785, hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h2787, hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h1, h2361, h2886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h0, h2582, hc12, hc23, hlam, hphi, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h2887, hlam, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h0, h2582, h2887, hc12, hc23, hlam, hphi, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h2888, hlam, p2891_1]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [h2889, hlam, p2891_0]
                        · have p2891_0 := h2891c.1
                          have p2891_1 := h2891c.2.1
                          have p2891_2 := h2891c.2.2.1
                          have p2891_3 := h2891c.2.2.2
                          linarith only [hlam, p2891_0]
                      · linarith only [h1, h2783, h2789, h2886, h2890, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h2361, h2781, h2789, h2886, h2889, hc12, hc23, hlam, hphi]
                  · linarith only [h2, h2781, h2783, h2789, h2888, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h2, h2781, h2887, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2921 | h2921
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2922 | h2922
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2923 | h2923
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2924 | h2924
                      · linarith only [h2, h2781, h2785, h2886, h2924, hc12, hc23, hlam, hphi]
                      · linarith only [h2, h2781, h2782, h2783, h2789, h2924, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h2, h2361, h2781, h2782, h2923, hc12, hc23, hlam, hphi]
                  · linarith only [h2, h2781, h2783, h2789, h2922, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h2, h2781, h2782, h2783, h2789, h2886, h2921, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2930 | h2930
      · linarith only [h0, h2, h2930, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2932 | h2932
        · linarith only [h0, h2361, h2932, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2934 | h2934
          · linarith only [h0, h2582, h2934, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2936 | h2936
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2937 | h2937
              · linarith only [h1, h2782, h2937, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2939 | h2939
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2940 | h2940
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2941 | h2941
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2942 | h2942
                      · linarith only [h0, h2, h2361, h2781, h2782, h2942, hc12, hc23, hlam, hphi]
                      · rcases h2bigk with h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2361, h2782, h2941, hc12, hc24, hlam, hphi, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2, hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2361, hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2582, hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h0, hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2930, hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2932, hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2934, hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2782, h2941, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h0, h2361, h2782, h2941, hc12, hc23, hlam, hphi, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2939, hlam, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h0, h2361, h2782, h2939, h2941, hc12, hc23, hlam, hphi, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2940, hlam, p2944_1]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [h2941, hlam, p2944_0]
                        · have p2944_0 := h2944c.1
                          have p2944_1 := h2944c.2.1
                          have p2944_2 := h2944c.2.2.1
                          have p2944_3 := h2944c.2.2.2
                          linarith only [hlam, p2944_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2970 | h2970
                      · linarith only [h0, h2361, h2941, h2970, hc12, hc34, hlam, hphi, ht23]
                      · rcases h2bigk with h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2361, hc12, hc24, hlam, hphi, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2, hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2361, hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2582, hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h0, hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2930, hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2932, hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2934, hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h0, h2361, hc12, hc23, hlam, hphi, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h0, h2582, hc12, hc23, hlam, hphi, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2941, hc12, hc45, hlam, hphi, ht23, ht34, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2939, hlam, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [hlam, p2972_0]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2941, hlam, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2940, hlam, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [h2361, h2941, hc04, hc45, hlam, hphi, p2972_1]
                        · have p2972_0 := h2972c.1
                          have p2972_1 := h2972c.2.1
                          have p2972_2 := h2972c.2.2.1
                          have p2972_3 := h2972c.2.2.2
                          linarith only [hlam, p2972_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2998 | h2998
                    · linarith only [h0, h2361, h2782, h2939, h2940, h2998, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3000 | h3000
                      · linarith only [h0, h2361, h2998, h3000, hc12, hc34, hlam, hphi, ht23]
                      · rcases h2bigk with h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2361, hc12, hc24, hlam, hphi, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2, hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2361, hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2582, hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h0, hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2930, hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2932, hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2934, hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2940, h3000, hc02, hc45, hlam, hphi, ht23, ht34, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2940, h3000, hc12, hc45, hlam, hphi, ht23, ht34, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2940, h3000, hc24, hc45, hlam, hphi, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2940, hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2939, hlam, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [hlam, p3002_0]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2998, hlam, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h0, h2940, h3000, hc12, hc45, hlam, hphi, ht23, ht34, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2940, h3000, hc12, hc45, hlam, hphi, ht23, ht34, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h2, h2940, h3000, hc03, hc45, hlam, hphi, ht34, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [h0, h2361, h2940, h3000, hc12, hc45, hlam, hphi, ht23, ht34, p3002_1]
                        · have p3002_0 := h3002c.1
                          have p3002_1 := h3002c.2.1
                          have p3002_2 := h3002c.2.2.1
                          have p3002_3 := h3002c.2.2.2
                          linarith only [hlam, p3002_0]
                · linarith only [h2, h2781, h2939, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3029 | h3029
              · linarith only [h2781, h2782, h2936, h3029, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3031 | h3031
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3032 | h3032
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3033 | h3033
                    · linarith only [h2781, h2782, h2930, h2936, h3033, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3035 | h3035
                      · linarith only [h2361, h2781, h3033, h3035, hlam]
                      · rcases h2bigk with h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h2, hc12, hc23, hlam, hphi, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h2, hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h2361, hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h2582, hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h0, hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h2930, hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h2932, hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h2934, hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h2361, h2781, h2930, h2936, hc12, hc23, hlam, hphi, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h0, h2582, hc12, hc23, hlam, hphi, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h3033, hc12, hc45, hlam, hphi, ht23, ht34, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h3031, hlam, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [hlam, p3037_0]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h3033, hlam, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h3032, hlam, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [h3033, hc24, hc45, hlam, hphi, p3037_1]
                        · have p3037_0 := h3037c.1
                          have p3037_1 := h3037c.2.1
                          have p3037_2 := h3037c.2.2.1
                          have p3037_3 := h3037c.2.2.2
                          linarith only [hlam, p3037_0]
                  · linarith only [h2, h2781, h2930, h2936, h3032, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h2, h2781, h3031, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3065 | h3065
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3066 | h3066
      · linarith only [h0, h2, h3066, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3068 | h3068
        · linarith only [h0, h2361, h3068, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3070 | h3070
          · linarith only [h0, h2582, h3070, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3072 | h3072
            · linarith only [h1, h2781, h3072, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3074 | h3074
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3075 | h3075
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3076 | h3076
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3077 | h3077
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3078 | h3078
                      · rcases h2bigk with h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h2, h2781, h3075, hc12, hc24, hlam, hphi, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h2, hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h2361, hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h2582, hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h0, hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h3066, hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h3068, hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h3070, hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h0, h2361, hc12, hc23, hlam, hphi, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h0, h2582, hc12, hc23, hlam, hphi, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h3075, hlam, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h0, h2582, h3075, hc12, hc23, hlam, hphi, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h3076, hlam, p3079_1]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [h3077, hlam, p3079_0]
                        · have p3079_0 := h3079c.1
                          have p3079_1 := h3079c.2.1
                          have p3079_2 := h3079c.2.2.1
                          have p3079_3 := h3079c.2.2.2
                          linarith only [hlam, p3079_0]
                      · linarith only [h1, h2781, h3074, h3078, hlam]
                    · linarith only [h0, h1, h2361, h2781, h3074, h3075, h3077, hc12, hc23, hlam, hphi]
                  · linarith only [h2781, h3075, h3076, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3108 | h3108
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3109 | h3109
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3110 | h3110
                      · rcases h2bigk with h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h2582, h3108, hc12, hc23, hlam, hphi, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h2, hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h2361, hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h2582, hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h0, hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3066, hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3068, hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3070, hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3075, hc02, hc34, hlam, hphi, ht23, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3075, hc12, hc34, hlam, hphi, ht23, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3075, hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3075, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3075, hc23, hc34, hlam, hphi, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h0, h2582, h3075, hc12, hc34, hlam, hphi, ht23, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h0, h3108, hc12, hc23, hlam, hphi, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3108, hc12, hc23, hlam, hphi, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3108, hlam, p3111_1]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [h3109, hlam, p3111_0]
                        · have p3111_0 := h3111c.1
                          have p3111_1 := h3111c.2.1
                          have p3111_2 := h3111c.2.2.1
                          have p3111_3 := h3111c.2.2.2
                          linarith only [hlam, p3111_0]
                      · linarith only [h1, h3074, h3075, h3110, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2361, h3065, h3109, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3139 | h3139
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3140 | h3140
                      · rcases h2bigk with h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c | h3141c
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h2, hc12, hc23, hlam, hphi, p3141_1]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h2, hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h2361, hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h2582, hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h0, hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h3066, hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h3068, hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h3070, hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p3141_1]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h3108, h3140, hc12, hc34, hlam, hphi, ht23, p3141_1]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h3075, hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h3108, hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p3141_1]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p3141_1]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h3066, h3075, hc13, hc34, hlam, hphi, p3141_1]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h0, h2582, h3075, hc12, hc34, hlam, hphi, ht23, p3141_1]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p3141_1]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p3141_1]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h0, h2, h3108, h3140, hc12, hc34, hlam, hphi, ht23, p3141_1]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [h3139, hlam, p3141_0]
                        · have p3141_0 := h3141c.1
                          have p3141_1 := h3141c.2.1
                          have p3141_2 := h3141c.2.2.1
                          have p3141_3 := h3141c.2.2.2
                          linarith only [hlam, p3141_0]
                      · linarith only [h1, h2361, h3074, h3075, h3140, hlam]
                    · linarith only [h1, h2361, h3074, h3139, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3169 | h3169
                · linarith only [h2781, h3065, h3068, h3074, h3169, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3171 | h3171
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3172 | h3172
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3173 | h3173
                      · linarith only [h3066, h3072, h3074, h3169, h3171, h3173, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h3065, h3169, h3171, h3173, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h2361, h2582, h3065, h3169, h3171, h3172, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3177 | h3177
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3178 | h3178
                      · rcases h2bigk with h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h2, hc12, hc23, hlam, hphi, p3179_1]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h2, hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h2361, hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h2582, hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h0, hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h3066, hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h3068, hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h3070, hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p3179_1]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h3171, hc12, hc35, hlam, hphi, ht23, p3179_1]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h3169, hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h3171, hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p3179_1]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p3179_1]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h3169, hc23, hc34, hlam, hphi, p3179_1]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h0, h2582, h3169, hc12, hc34, hlam, hphi, ht23, p3179_1]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p3179_1]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p3179_1]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h0, h2, h3171, hc12, hc35, hlam, hphi, ht23, p3179_1]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [h3177, hlam, p3179_0]
                        · have p3179_0 := h3179c.1
                          have p3179_1 := h3179c.2.1
                          have p3179_2 := h3179c.2.2.1
                          have p3179_3 := h3179c.2.2.2
                          linarith only [hlam, p3179_0]
                      · linarith only [h2361, h3065, h3169, h3178, hlam]
                    · linarith only [h2361, h3065, h3177, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3207 | h3207
      · linarith only [h0, h2, h3207, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3209 | h3209
        · linarith only [h0, h2361, h3209, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3211 | h3211
          · linarith only [h0, h2582, h3211, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3213 | h3213
            · linarith only [h1, h2781, h3213, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3215 | h3215
              · linarith only [h1, h3065, h3215, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3217 | h3217
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3218 | h3218
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3219 | h3219
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3220 | h3220
                      · linarith only [h0, h2361, h3065, h3217, h3220, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h2, h2781, h3217, h3219, h3220, hc12, hc23, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3223 | h3223
                      · linarith only [h0, h2361, h3219, h3223, hc12, hc34, hlam, hphi, ht23]
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
                          linarith only [h2, h2781, h3217, hc12, hc24, hlam, hphi, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h2, hlam, p3225_0]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h2361, hlam, p3225_0]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h2582, hlam, p3225_0]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h0, hlam, p3225_0]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [hlam, p3225_0]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h3207, hlam, p3225_0]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h3209, hlam, p3225_0]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h3211, hlam, p3225_0]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [hlam, p3225_0]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h0, h2361, hc12, hc23, hlam, hphi, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h0, h2582, hc12, hc23, hlam, hphi, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h3217, hlam, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [hlam, p3225_0]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h3219, hlam, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h3218, hlam, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [h2781, h3217, h3219, hc03, hc45, hlam, hphi, ht34, p3225_1]
                        · have p3225_0 := h3225c.1
                          have p3225_1 := h3225c.2.1
                          have p3225_2 := h3225c.2.2.1
                          have p3225_3 := h3225c.2.2.2
                          linarith only [hlam, p3225_0]
                  · linarith only [h0, h2, h2781, h3217, h3218, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3252 | h3252
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3253 | h3253
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3254 | h3254
                      · linarith only [h1, h3065, h3207, h3213, h3217, h3252, h3254, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h3217, h3252, h3253, h3254, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h3217, h3252, h3253, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3258 | h3258
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3259 | h3259
                      · rcases h2bigk with h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h2, h2781, h3065, h3258, hc12, hc25, hlam, hphi, p3260_1]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h2, hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h2361, hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h2582, hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h0, hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h3207, hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h3209, hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h3211, hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h3252, hc02, hc35, hlam, hphi, ht23, p3260_1]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h3252, hc12, hc35, hlam, hphi, ht23, p3260_1]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h3217, hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h3252, hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h0, h3217, hc12, hc34, hlam, hphi, ht23, p3260_1]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h3217, hc12, hc34, hlam, hphi, ht23, p3260_1]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h3217, hc23, hc34, hlam, hphi, p3260_1]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h0, h2582, h3217, hc12, hc34, hlam, hphi, ht23, p3260_1]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p3260_1]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p3260_1]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h0, h2, h3252, hc12, hc35, hlam, hphi, ht23, p3260_1]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [h3258, hlam, p3260_0]
                        · have p3260_0 := h3260c.1
                          have p3260_1 := h3260c.2.1
                          have p3260_2 := h3260c.2.2.1
                          have p3260_3 := h3260c.2.2.2
                          linarith only [hlam, p3260_0]
                      · linarith only [h3217, h3258, h3259, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3287 | h3287
                      · linarith only [h0, h2, h3217, h3258, h3287, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2, h3217, h3287, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2361 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h2582 | h2582
  · exact r1l7_22_14_H_I_L_I_s1_x1_x1_x0 m hb2 hb4 hg0 hg1 h2 h2361 h2582
  · exact r1l7_22_14_H_I_L_I_s1_x1_x1_x1 m hb2 hb4 hg0 hg1 h2 h2361 h2582

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 4 (by decide) (by decide) with h2361 | h2361
  · exact r1l7_22_14_H_I_L_I_s1_x1_x0 m hb2 hb4 hg0 hg1 h2 h2361
  · exact r1l7_22_14_H_I_L_I_s1_x1_x1 m hb2 hb4 hg0 hg1 h2 h2361

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
  · exact r1l7_22_14_H_I_L_I_s1_x0 m hb2 hb4 hg0 hg1 h2
  · exact r1l7_22_14_H_I_L_I_s1_x1 m hb2 hb4 hg0 hg1 h2

end R2N4
