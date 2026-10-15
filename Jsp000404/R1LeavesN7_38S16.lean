import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_38S14
import Jsp000404.R1LeavesN7_38S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1662 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2282 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2613 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2842 | h2842
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2843 | h2843
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2844 | h2844
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2845 | h2845
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2846 | h2846
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2847 | h2847
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2848 | h2848
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2849 | h2849
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2850 | h2850
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2851 | h2851
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2852 | h2852
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2853 | h2853
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2854 | h2854
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2855 | h2855
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2856 | h2856
                              · rcases h0bigk with h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [hlam, p2857_0]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h0, hlam, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h1662, hlam, p2857_0]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h2282, hlam, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h2613, hlam, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [hlam, p2857_0]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h0, h2842, h2853, h2856, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h0, h2282, hc01, hc12, hlam, hphi, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h0, h2613, hc01, hc12, hlam, hphi, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h1662, hc01, hc13, hlam, hphi, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h2842, hlam, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [hlam, p2857_0]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h1662, h2282, hc01, hlam, hphi, ht12, ht23, p2857_1, u3elo1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h1662, h2613, hc01, hlam, hphi, ht12, ht23, p2857_1, u3elo1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h2282, h2849, hc01, hc12, hlam, hphi, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h2843, hlam, p2857_0]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h2845, hlam, p2857_0]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [hlam, p2857_0]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h1662, h2613, h2845, hc01, hlam, hphi, ht12, ht23, p2857_1, u3elo1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h2613, hc01, hc15, hlam, hphi, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h2844, hlam, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h2846, hlam, p2857_0]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [h2847, hlam, p2857_1]
                                · have p2857_0 := h2857c.1
                                  have p2857_1 := h2857c.2.1
                                  have p2857_2 := h2857c.2.2.1
                                  have p2857_3 := h2857c.2.2.2
                                  linarith only [hlam, p2857_0]
                              · rcases h0bigk with h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c | h2883c
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [hlam, p2883_0]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h0, hlam, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h1662, hlam, p2883_0]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h2282, hlam, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h2613, hlam, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [hlam, p2883_0]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h0, h1662, hc01, hc12, hlam, hphi, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h0, h2613, h2847, hc01, hc12, hlam, hphi, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h0, h2613, hc01, hc12, hlam, hphi, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p2883_1, u3elo0]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h2842, hlam, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [hlam, p2883_0]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h1662, h2843, h2855, h2856, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2883_1, u3elo1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h1662, h2613, hc01, hlam, hphi, ht12, ht23, p2883_1, u3elo1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h2282, h2849, hc01, hc12, hlam, hphi, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h2843, hlam, p2883_0]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h2845, hlam, p2883_0]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [hlam, p2883_0]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h1662, h2613, h2845, hc01, hlam, hphi, ht12, ht23, p2883_1, u3elo1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h2613, h2851, hc01, hlam, hphi, ht12, ht23, p2883_1, u3elo1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h2844, hlam, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h2846, hlam, p2883_0]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [h2847, hlam, p2883_1]
                                · have p2883_0 := h2883c.1
                                  have p2883_1 := h2883c.2.1
                                  have p2883_2 := h2883c.2.2.1
                                  have p2883_3 := h2883c.2.2.2
                                  linarith only [hlam, p2883_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2909 | h2909
                              · linarith only [h1662, h2845, h2855, h2909, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · rcases h0bigk with h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [hlam, p2911_0]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h0, hlam, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h1662, hlam, p2911_0]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h2282, hlam, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h2613, hlam, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [hlam, p2911_0]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h0, h1662, hc01, hc12, hlam, hphi, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h0, h2613, h2847, hc01, hc12, hlam, hphi, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h0, h2613, hc01, hc12, hlam, hphi, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p2911_1, u3elo0]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h2842, hlam, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [hlam, p2911_0]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h1662, h2613, h2847, hc01, hlam, hphi, ht12, ht23, p2911_1, u3elo1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h1662, h2613, hc01, hlam, hphi, ht12, ht23, p2911_1, u3elo1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h2282, h2849, hc01, hc12, hlam, hphi, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h2843, hlam, p2911_0]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h2845, hlam, p2911_0]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [hlam, p2911_0]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h1662, h2613, h2845, hc01, hlam, hphi, ht12, ht23, p2911_1, u3elo1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h2613, h2851, hc01, hlam, hphi, ht12, ht23, p2911_1, u3elo1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h2844, hlam, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h2846, hlam, p2911_0]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [h2847, hlam, p2911_1]
                                · have p2911_0 := h2911c.1
                                  have p2911_1 := h2911c.2.1
                                  have p2911_2 := h2911c.2.2.1
                                  have p2911_3 := h2911c.2.2.2
                                  linarith only [hlam, p2911_0]
                          · linarith only [h1662, h2846, h2854, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1662, h2845, h2853, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1662, h2282, h2845, h2847, h2852, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1662, h2846, h2851, hlam]
                  · linarith only [h0, h1662, h2844, h2845, h2847, h2850, hc01, hlam, hphi, ht12, ht23, u3elo1]
                · linarith only [h0, h2843, h2849, hlam]
              · linarith only [h0, h2848, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2944 | h2944
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2945 | h2945
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2946 | h2946
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2947 | h2947
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2948 | h2948
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2949 | h2949
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2950 | h2950
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2951 | h2951
                            · linarith only [h2843, h2847, h2951, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2953 | h2953
                              · linarith only [h2282, h2847, h2953, hc01, hlam, hphi, ht12, ht23, u3elo3]
                              · rcases h0bigk with h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [hlam, p2955_0]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h0, hlam, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h1662, hlam, p2955_0]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h2282, hlam, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h2613, hlam, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [hlam, p2955_0]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h0, h2842, h2950, h2953, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h0, h2282, hc01, hc12, hlam, hphi, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h0, h2613, hc01, hc12, hlam, hphi, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p2955_1, u3elo0]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h2842, hlam, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [hlam, p2955_0]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h1662, h2282, hc01, hlam, hphi, ht12, ht23, p2955_1, u3elo1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h1662, h2613, hc01, hlam, hphi, ht12, ht23, p2955_1, u3elo1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h2847, h2948, hc01, hc14, hlam, hphi, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h2843, hlam, p2955_0]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h2845, hlam, p2955_0]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [hlam, p2955_0]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h2847, hlam, p2955_0]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h2613, hc01, hc15, hlam, hphi, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h2844, hlam, p2955_1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h2846, hlam, p2955_0]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [h1662, h2846, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2955_1, u3elo1]
                                · have p2955_0 := h2955c.1
                                  have p2955_1 := h2955c.2.1
                                  have p2955_2 := h2955c.2.2.1
                                  have p2955_3 := h2955c.2.2.2
                                  linarith only [hlam, p2955_0]
                          · linarith only [h1662, h2846, h2950, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1662, h2845, h2949, hc23, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2983 | h2983
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2984 | h2984
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2985 | h2985
                            · linarith only [h2282, h2948, h2985, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2987 | h2987
                              · linarith only [h2282, h2948, h2983, h2987, hc01, hc23, hlam, hphi, ht12]
                              · rcases h0bigk with h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c | h2989c
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [hlam, p2989_0]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h0, hlam, p2989_1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h1662, hlam, p2989_0]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2282, hlam, p2989_1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2613, hlam, p2989_1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2989_1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [hlam, p2989_0]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h0, h2842, h2984, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2989_1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h0, h2282, hc01, hc12, hlam, hphi, p2989_1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h0, h2613, hc01, hc12, hlam, hphi, p2989_1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p2989_1, u3elo0]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2842, hlam, p2989_1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [hlam, p2989_0]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h1662, h2282, hc01, hlam, hphi, ht12, ht23, p2989_1, u3elo1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h1662, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2989_1, u3elo1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2282, hc01, hc14, hlam, hphi, p2989_1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2843, hlam, p2989_0]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2845, hlam, p2989_0]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [hlam, p2989_0]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2847, hlam, p2989_0]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2613, h2947, hc01, hlam, hphi, ht12, ht23, p2989_1, u3elo1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2844, hlam, p2989_1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2846, hlam, p2989_0]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [h2613, h2947, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2989_1, u3elo1]
                                · have p2989_0 := h2989c.1
                                  have p2989_1 := h2989c.2.1
                                  have p2989_2 := h2989c.2.2.1
                                  have p2989_3 := h2989c.2.2.2
                                  linarith only [hlam, p2989_0]
                          · linarith only [h1662, h2846, h2983, h2984, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1662, h2845, h2983, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1662, h2846, h2947, hlam]
                  · linarith only [h0, h2844, h2946, hlam]
                · linarith only [h0, h2843, h2945, hlam]
              · linarith only [h0, h2944, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3021 | h3021
            · linarith only [h2845, h2846, h3021, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3023 | h3023
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3024 | h3024
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3025 | h3025
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3026 | h3026
                    · linarith only [h2845, h2846, h3026, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h1662, h3026, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h2844, h3025, hlam]
                · linarith only [h0, h2843, h2845, h3024, hc01, hlam, hphi, ht12, ht23, u3elo0]
              · linarith only [h0, h3023, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3032 | h3032
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3033 | h3033
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3034 | h3034
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3035 | h3035
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3036 | h3036
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3037 | h3037
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3038 | h3038
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3039 | h3039
                        · linarith only [h2842, h2845, h3032, h3039, hc02, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3041 | h3041
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3042 | h3042
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3043 | h3043
                              · rcases h0bigk with h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c | h3044c
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [hlam, p3044_0]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h0, hlam, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h1662, hlam, p3044_0]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2282, hlam, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2613, hlam, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [hlam, p3044_0]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h0, h2842, h3041, h3043, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h0, h2842, h2845, h3041, h3043, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h0, h2613, hc01, hc12, hlam, hphi, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2845, hc01, hlam, hphi, ht12, ht23, p3044_1, u3elo3]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2842, hlam, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [hlam, p3044_0]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2845, hlam, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2613, h2845, hc01, hlam, hphi, ht12, ht23, p3044_1, u3elo3]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2282, hc01, hc14, hlam, hphi, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2843, hlam, p3044_0]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2842, h2845, h3041, h3043, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3044_1, u3elo3]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [hlam, p3044_0]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2613, h2845, hc01, hlam, hphi, ht12, ht23, p3044_1, u3elo3]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2613, h3037, hc01, hc13, hlam, hphi, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h2844, hlam, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h3032, hlam, p3044_0]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [h3033, hlam, p3044_1]
                                · have p3044_0 := h3044c.1
                                  have p3044_1 := h3044c.2.1
                                  have p3044_2 := h3044c.2.2.1
                                  have p3044_3 := h3044c.2.2.2
                                  linarith only [hlam, p3044_0]
                              · linarith only [h2842, h2845, h3033, h3041, h3043, hc04, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h2845, h3032, h3033, h3039, h3041, h3042, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h2845, h3032, h3041, hc23, hlam, hphi, u3elo3]
                      · linarith only [h2282, h2845, h3032, h3033, h3038, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2845, h3032, h3037, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h2844, h2845, h3032, h3036, hc02, hlam, hphi, ht23, u3elo3]
                · linarith only [h0, h2843, h3035, hlam]
              · linarith only [h0, h3034, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2845, h3032, h3033, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3079 | h3079
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3080 | h3080
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3081 | h3081
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3082 | h3082
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3083 | h3083
                    · linarith only [h3032, h3083, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1662, h3083, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h2844, h3082, hlam]
                · linarith only [h0, h2843, h3081, hlam]
              · linarith only [h0, h3080, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3089 | h3089
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3090 | h3090
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3091 | h3091
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3092 | h3092
                    · linarith only [h1662, h3032, h3092, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1662, h3092, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h2844, h3091, hlam]
                · linarith only [h0, h2843, h3090, hlam]
              · linarith only [h0, h2842, h3089, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3098 | h3098
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3099 | h3099
          · linarith only [h2842, h2844, h3099, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3101 | h3101
            · linarith only [h2842, h2844, h3098, h3099, h3101, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3103 | h3103
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3104 | h3104
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3105 | h3105
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3106 | h3106
                    · linarith only [h2282, h3098, h3099, h3106, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1662, h3106, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3109 | h3109
                    · linarith only [h3098, h3099, h3109, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h1662, h3109, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h0, h2843, h3104, hlam]
              · linarith only [h0, h3103, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3114 | h3114
          · linarith only [h2842, h2844, h3114, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3116 | h3116
            · linarith only [h2843, h2844, h3116, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3118 | h3118
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3119 | h3119
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3120 | h3120
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3121 | h3121
                    · linarith only [h1662, h3114, h3121, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1662, h3121, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3124 | h3124
                    · linarith only [h1662, h3114, h3118, h3120, h3124, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h1662, h3124, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h0, h2843, h3119, hlam]
              · linarith only [h0, h2842, h3118, hc01, hlam, hphi, ht12, ht23, u3elo0]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3129 | h3129
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3130 | h3130
        · linarith only [h2842, h2843, h3130, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3132 | h3132
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3133 | h3133
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3134 | h3134
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3135 | h3135
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3136 | h3136
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3137 | h3137
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3138 | h3138
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3139 | h3139
                        · linarith only [h2842, h2843, h3130, h3135, h3139, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h2842, h2843, h3139, hc23, hlam, hphi, u3elo3]
                      · linarith only [h2842, h2843, h3133, h3135, h3138, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h3132, h3137, hc13, hlam, hphi, u3elo0]
                  · linarith only [h2843, h3129, h3135, h3136, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3145 | h3145
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3146 | h3146
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3147 | h3147
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3148 | h3148
                        · linarith only [h3130, h3148, hc03, hlam, hphi, u3elo2]
                        · linarith only [h2613, h3134, h3135, h3146, h3148, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h2282, h3132, h3133, h3147, hc01, hlam, hphi, ht12, ht23, u3elo0]
                    · linarith only [h1662, h3146, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h3129, h3145, hlam]
              · linarith only [h0, h3134, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2842, h2843, h3130, h3132, h3133, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3156 | h3156
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3157 | h3157
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3158 | h3158
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3159 | h3159
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3160 | h3160
                    · linarith only [h3132, h3160, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1662, h3160, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h2843, h3129, h3158, h3159, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3164 | h3164
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3165 | h3165
                    · linarith only [h1662, h3132, h3165, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1662, h3165, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h3129, h3164, hlam]
              · linarith only [h0, h3157, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2843, h3129, h3156, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3171 | h3171
        · linarith only [h2842, h2843, h3171, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3173 | h3173
          · linarith only [h2842, h3129, h3173, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3175 | h3175
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3176 | h3176
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3177 | h3177
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3178 | h3178
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3179 | h3179
                    · linarith only [h3173, h3179, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1662, h3179, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h2842, h2843, h3177, h3178, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3183 | h3183
                  · linarith only [h2842, h3129, h3177, h3183, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3185 | h3185
                    · linarith only [h1662, h3173, h3185, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1662, h3185, hc01, hlam, hphi, ht12, ht23, u3elo4]
              · linarith only [h0, h3176, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3189 | h3189
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3190 | h3190
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3191 | h3191
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3192 | h3192
                    · linarith only [h2842, h3129, h3173, h3192, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1662, h3192, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h2843, h3190, h3191, hc02, hc25, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3196 | h3196
                  · linarith only [h2842, h3129, h3190, h3196, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3198 | h3198
                    · linarith only [h1662, h3173, h3198, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1662, h3198, hc01, hlam, hphi, ht12, ht23, u3elo4]
              · linarith only [h0, h3189, hc01, hlam, hphi, ht12, ht23, u3elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3202 | h3202
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3203 | h3203
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3204 | h3204
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3205 | h3205
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3206 | h3206
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3207 | h3207
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3208 | h3208
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3209 | h3209
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3210 | h3210
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3211 | h3211
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3212 | h3212
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3213 | h3213
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3214 | h3214
                            · linarith only [h2842, h3202, h3207, h3214, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h2842, h3202, h3206, h3207, h3212, h3214, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h2842, h3213, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h2842, h3212, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h2842, h3202, h3206, h3211, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h2842, h3202, h3205, h3206, h3207, h3210, hlam]
                  · linarith only [h2842, h3203, h3207, h3209, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h2842, h3207, h3208, hc02, hc24, hlam, hphi]
              · linarith only [h0, h3207, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3224 | h3224
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3225 | h3225
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3226 | h3226
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3227 | h3227
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3228 | h3228
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3229 | h3229
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3230 | h3230
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3231 | h3231
                            · linarith only [h2842, h3202, h3206, h3224, h3231, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3233 | h3233
                              · linarith only [h2282, h2842, h3203, h3206, h3224, h3229, h3231, h3233, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases h0bigk with h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [hlam, p3235_0]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h0, hlam, p3235_1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h1662, hlam, p3235_0]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2282, hlam, p3235_1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2613, hlam, p3235_1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2842, h3224, hc01, hlam, hphi, ht12, ht23, p3235_1, u3elo1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [hlam, p3235_0]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2842, hlam, p3235_0]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2282, h2842, h3224, hc01, hlam, hphi, ht12, ht23, p3235_1, u3elo1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2842, h3224, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3235_1, u3elo1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2842, h3224, hc01, hlam, hphi, ht12, ht23, p3235_1, u3elo1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2842, h3224, hc02, hlam, hphi, ht23, p3235_1, u3elo1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [hlam, p3235_0]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2282, h2842, h3224, hc01, hlam, hphi, ht12, ht23, p3235_1, u3elo1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2613, h2842, h3224, hc01, hlam, hphi, ht12, ht23, p3235_1, u3elo1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h3206, h3228, hc01, hc14, hlam, hphi, p3235_1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h3202, hlam, p3235_0]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h3204, hlam, p3235_0]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [hlam, p3235_0]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h3206, hlam, p3235_0]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2613, hc01, hc15, hlam, hphi, p3235_1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h3203, hlam, p3235_1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h3205, hlam, p3235_0]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [h2842, h3203, h3224, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3235_1, u3elo1]
                                · have p3235_0 := h3235c.1
                                  have p3235_1 := h3235c.2.1
                                  have p3235_2 := h3235c.2.2.1
                                  have p3235_3 := h3235c.2.2.2
                                  linarith only [hlam, p3235_0]
                          · linarith only [h2842, h3230, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h2842, h3202, h3229, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3263 | h3263
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3264 | h3264
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3265 | h3265
                            · linarith only [h2842, h3202, h3228, h3265, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3267 | h3267
                              · linarith only [h2282, h3203, h3228, h3263, h3265, h3267, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases h0bigk with h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c | h3269c
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [hlam, p3269_0]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h0, hlam, p3269_1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h1662, hlam, p3269_0]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2282, hlam, p3269_1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2613, hlam, p3269_1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2842, h3224, hc01, hlam, hphi, ht12, ht23, p3269_1, u3elo1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [hlam, p3269_0]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2842, hlam, p3269_0]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2282, h2842, h3224, hc01, hlam, hphi, ht12, ht23, p3269_1, u3elo1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2282, h2842, h3206, h3224, hc01, hlam, hphi, ht12, ht23, p3269_1, u3elo1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2842, h3224, hc01, hlam, hphi, ht12, ht23, p3269_1, u3elo1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2842, h3203, h3224, h3263, h3265, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3269_1, u3elo1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [hlam, p3269_0]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2282, h2842, h3224, hc01, hlam, hphi, ht12, ht23, p3269_1, u3elo1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2282, h2842, h3206, h3224, hc01, hlam, hphi, ht12, ht23, p3269_1, u3elo1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2282, hc01, hc14, hlam, hphi, p3269_1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h3202, hlam, p3269_0]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h3204, hlam, p3269_0]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [hlam, p3269_0]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h3206, hlam, p3269_0]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h2613, h3227, hc01, hlam, hphi, ht12, ht23, p3269_1, u3elo1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h3203, hlam, p3269_1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h3205, hlam, p3269_0]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [h0, h2282, h3203, hc01, hc12, hlam, hphi, p3269_1]
                                · have p3269_0 := h3269c.1
                                  have p3269_1 := h3269c.2.1
                                  have p3269_2 := h3269c.2.2.1
                                  have p3269_3 := h3269c.2.2.2
                                  linarith only [hlam, p3269_0]
                          · linarith only [h2842, h3264, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h2842, h3202, h3263, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h2842, h3203, h3205, h3227, hc13, hlam, hphi, u3elo2]
                  · linarith only [h2842, h3203, h3224, h3226, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h2842, h3202, h3224, h3225, hlam]
              · linarith only [h0, h3224, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h2842, h3203, h3205, hlam]
        · linarith only [h2842, h3202, h3204, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3303 | h3303
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3304 | h3304
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3305 | h3305
            · linarith only [h3202, h3203, h3305, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3307 | h3307
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3308 | h3308
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3309 | h3309
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3310 | h3310
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3311 | h3311
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3312 | h3312
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3313 | h3313
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3314 | h3314
                            · linarith only [h3202, h3203, h3305, h3314, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3316 | h3316
                              · linarith only [h3203, h3314, h3316, hc02, hlam, hphi, ht23, u3elo3]
                              · rcases h0bigk with h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c | h3318c
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h0, hlam, p3318_1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h1662, hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h2282, hlam, p3318_1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h2613, hlam, p3318_1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h3203, h3308, h3311, h3314, hc01, hc12, hlam, hphi, p3318_1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h2842, hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h3203, h3308, h3311, h3314, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3318_1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h3203, hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h1662, hc01, hlam, hphi, ht12, ht23, p3318_1, u3elo1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h2842, h3307, hc02, hlam, hphi, ht23, p3318_1, u3elo1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h2282, h2842, h3307, hc01, hlam, hphi, ht12, ht23, p3318_1, u3elo1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h2842, h3307, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3318_1, u3elo1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h2282, h3308, hc01, hc12, hlam, hphi, p3318_1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h3202, hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h3303, hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h3305, hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h2613, h3310, hc01, hlam, hphi, ht12, ht23, p3318_1, u3elo1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h3203, h3310, h3311, h3314, hc02, hlam, hphi, ht23, p3318_1, u3elo1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h3304, hlam, p3318_0]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [h2282, h3203, h3310, h3311, h3314, hc01, hlam, hphi, ht12, ht23, p3318_1, u3elo1]
                                · have p3318_0 := h3318c.1
                                  have p3318_1 := h3318c.2.1
                                  have p3318_2 := h3318c.2.2.1
                                  have p3318_3 := h3318c.2.2.2
                                  linarith only [hlam, p3318_0]
                          · linarith only [h2842, h3304, h3313, hlam]
                        · linarith only [h2842, h3312, hc02, hlam, hphi, ht23, u3elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3346 | h3346
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3347 | h3347
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3348 | h3348
                            · linarith only [h2282, h3202, h3311, h3348, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3350 | h3350
                              · linarith only [h2282, h3202, h3203, h3309, h3310, h3311, h3346, h3350, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases h0bigk with h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c | h3352c
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h0, hlam, p3352_1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h1662, hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2282, hlam, p3352_1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2613, hlam, p3352_1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h3203, h3309, h3310, hc01, hlam, hphi, ht12, ht23, p3352_1, u3elo1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2842, hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2282, h3203, h3309, h3310, hc01, hlam, hphi, ht12, ht23, p3352_1, u3elo1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h3203, hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2842, h3307, hc01, hlam, hphi, ht12, ht23, p3352_1, u3elo1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2842, h3202, h3307, h3346, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3352_1, u3elo1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2282, h2842, h3307, hc01, hlam, hphi, ht12, ht23, p3352_1, u3elo1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2842, h3307, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3352_1, u3elo1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2282, hc01, hc14, hlam, hphi, p3352_1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h3202, hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h3303, hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h3305, hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2613, h3310, hc01, hlam, hphi, ht12, ht23, p3352_1, u3elo1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h3203, h3309, h3310, hc02, hlam, hphi, ht23, p3352_1, u3elo1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h3304, hlam, p3352_0]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [h2282, h3203, h3309, h3310, hc01, hlam, hphi, ht12, ht23, p3352_1, u3elo1]
                                · have p3352_0 := h3352c.1
                                  have p3352_1 := h3352c.2.1
                                  have p3352_2 := h3352c.2.2.1
                                  have p3352_3 := h3352c.2.2.2
                                  linarith only [hlam, p3352_0]
                          · linarith only [h2842, h3202, h3346, h3347, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h2842, h3346, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h3304, h3310, hc13, hlam, hphi, u3elo0]
                  · linarith only [h2842, h3202, h3307, h3309, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h2842, h3202, h3307, h3308, hlam]
              · linarith only [h0, h3307, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3384 | h3384
            · linarith only [h3202, h3203, h3384, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3386 | h3386
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3387 | h3387
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3388 | h3388
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3389 | h3389
                    · linarith only [h2842, h3304, h3389, hc02, hlam, hphi, ht23, u3elo1]
                    · linarith only [h1662, h3389, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h2842, h3202, h3386, h3388, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h2842, h3202, h3386, h3387, hlam]
              · linarith only [h0, h3386, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h2842, h3202, h3303, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3396 | h3396
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3397 | h3397
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3398 | h3398
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3399 | h3399
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3400 | h3400
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3401 | h3401
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3402 | h3402
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3403 | h3403
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3404 | h3404
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3405 | h3405
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3406 | h3406
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3407 | h3407
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3408 | h3408
                              · rcases h0bigk with h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [hlam, p3409_0]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h0, hlam, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h1662, hlam, p3409_0]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h2282, hlam, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h2613, hlam, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h3202, hc01, hc24, hlam, hphi, ht12, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [hlam, p3409_0]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h2842, hlam, p3409_0]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h3202, hlam, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h3202, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p3409_1, u3elo0]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h2842, h3400, hc02, hlam, hphi, ht23, p3409_1, u3elo1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [hlam, p3409_0]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h2842, h3400, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3409_1, u3elo1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h2613, h2842, h3400, hc01, hlam, hphi, ht12, ht23, p3409_1, u3elo1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h2282, hc01, hc14, hlam, hphi, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h3202, h3396, h3406, h3408, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h3397, hlam, p3409_0]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [hlam, p3409_0]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h2613, h2842, h3397, h3400, hc01, hlam, hphi, ht12, ht23, p3409_1, u3elo1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h2613, hc01, hc15, hlam, hphi, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h3396, hlam, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h3398, hlam, p3409_0]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [h3399, hlam, p3409_1]
                                · have p3409_0 := h3409c.1
                                  have p3409_1 := h3409c.2.1
                                  have p3409_2 := h3409c.2.2.1
                                  have p3409_3 := h3409c.2.2.2
                                  linarith only [hlam, p3409_0]
                              · linarith only [h2842, h3396, h3400, h3407, h3408, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h2613, h3202, h3399, h3403, h3407, hc02, hlam, hphi, ht23, u3elo1]
                          · linarith only [h3202, h3405, h3406, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h2613, h2842, h3396, h3405, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h2282, h3397, h3399, h3404, hc01, hlam, hphi, ht12, ht23, u3elo0]
                    · linarith only [h1662, h3403, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h2842, h3396, h3402, hc12, hc23, hlam, hphi]
                · linarith only [h2842, h3400, h3401, hc02, hc24, hlam, hphi]
              · linarith only [h0, h3400, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h3202, h3396, h3399, hlam]
          · linarith only [h3202, h3396, h3397, h3398, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3446 | h3446
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3447 | h3447
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3448 | h3448
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3449 | h3449
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3450 | h3450
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3451 | h3451
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3452 | h3452
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3453 | h3453
                        · linarith only [h2842, h3396, h3397, h3448, h3453, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h2842, h3396, h3453, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h3202, h3396, h3447, h3449, h3452, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h3446, h3451, hc13, hlam, hphi, u3elo0]
                  · linarith only [h2842, h3396, h3448, h3450, hlam]
                · linarith only [h2842, h3396, h3448, h3449, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h3448, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h3202, h3396, h3447, hlam]
          · linarith only [h2842, h3396, h3446, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3463 | h3463
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3464 | h3464
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3465 | h3465
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3466 | h3466
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3467 | h3467
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3468 | h3468
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3469 | h3469
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3470 | h3470
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3471 | h3471
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3472 | h3472
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3473 | h3473
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3474 | h3474
                              · rcases h0bigk with h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [hlam, p3475_0]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h0, hlam, p3475_1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h1662, hlam, p3475_0]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h2282, hlam, p3475_1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h2613, hlam, p3475_1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h3396, h3466, h3471, h3473, hc01, hlam, hphi, ht12, ht23, p3475_1, u3elo1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [hlam, p3475_0]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h2842, hlam, p3475_0]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h3202, hlam, p3475_1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h3396, hlam, p3475_0]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p3475_1, u3elo0]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h2842, h3466, hc02, hlam, hphi, ht23, p3475_1, u3elo1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [hlam, p3475_0]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h0, h2842, h3396, h3465, h3466, hc01, hlam, hphi, ht12, ht23, p3475_1, u3elo1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h0, h2842, h3396, h3466, hc01, hlam, hphi, ht12, ht23, p3475_1, u3elo1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h2282, hc01, hc14, hlam, hphi, p3475_1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h0, h3202, h3466, h3471, hc01, hlam, hphi, ht12, ht23, p3475_1, u3elo1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h3463, hlam, p3475_0]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [hlam, p3475_0]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h0, h3202, h3396, h3466, h3471, hc01, hlam, hphi, ht12, ht23, p3475_1, u3elo1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h2613, h3469, hc01, hlam, hphi, ht12, ht23, p3475_1, u3elo1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h0, h3396, h3466, h3471, h3473, hc01, hlam, hphi, ht12, ht23, p3475_1, u3elo1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h3464, hlam, p3475_0]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [h3465, hlam, p3475_1]
                                · have p3475_0 := h3475c.1
                                  have p3475_1 := h3475c.2.1
                                  have p3475_2 := h3475c.2.2.1
                                  have p3475_3 := h3475c.2.2.2
                                  linarith only [hlam, p3475_0]
                              · rcases h0bigk with h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [hlam, p3501_0]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h0, hlam, p3501_1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h1662, hlam, p3501_0]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h2282, hlam, p3501_1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h2613, hlam, p3501_1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p3501_1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [hlam, p3501_0]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h2842, hlam, p3501_0]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h3202, hlam, p3501_1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h3396, hlam, p3501_0]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h2842, h3466, hc01, hlam, hphi, ht12, ht23, p3501_1, u3elo1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h2842, h3466, hc02, hlam, hphi, ht23, p3501_1, u3elo1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [hlam, p3501_0]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h2842, h3466, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3501_1, u3elo1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h2842, h3466, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3501_1, u3elo1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h2282, h3467, hc01, hc12, hlam, hphi, p3501_1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h0, h3202, h3466, h3471, hc01, hlam, hphi, ht12, ht23, p3501_1, u3elo1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h3463, hlam, p3501_0]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [hlam, p3501_0]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h0, h3202, h3396, h3466, h3471, hc01, hlam, hphi, ht12, ht23, p3501_1, u3elo1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h2613, h3469, hc01, hlam, hphi, ht12, ht23, p3501_1, u3elo1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h0, h3396, h3466, h3471, h3473, hc01, hlam, hphi, ht12, ht23, p3501_1, u3elo1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h3464, hlam, p3501_0]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [h3465, hlam, p3501_1]
                                · have p3501_0 := h3501c.1
                                  have p3501_1 := h3501c.2.1
                                  have p3501_2 := h3501c.2.2.1
                                  have p3501_3 := h3501c.2.2.2
                                  linarith only [hlam, p3501_0]
                            · linarith only [h3202, h3465, h3473, hlam]
                          · linarith only [h0, h2842, h3472, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h2842, h3471, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h2282, h2842, h3463, h3465, h3470, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h2842, h3464, h3466, h3469, hlam]
                  · linarith only [h0, h2842, h3466, h3468, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2842, h3466, h3467, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3466, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3535 | h3535
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3536 | h3536
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3537 | h3537
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3538 | h3538
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3539 | h3539
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3540 | h3540
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3541 | h3541
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3542 | h3542
                            · linarith only [h2282, h3465, h3535, h3540, h3542, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h0, h3202, h3539, h3542, hc01, hc14, hlam, hphi]
                          · linarith only [h3464, h3541, hc23, hlam, hphi, u3elo0]
                        · linarith only [h0, h2842, h3540, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3547 | h3547
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3548 | h3548
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3549 | h3549
                            · linarith only [h2282, h3539, h3547, h3549, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3551 | h3551
                              · linarith only [h0, h3202, h3463, h3536, h3539, h3551, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases h0bigk with h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c | h3553c
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [hlam, p3553_0]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h0, hlam, p3553_1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h1662, hlam, p3553_0]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h2282, hlam, p3553_1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h2613, hlam, p3553_1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h3202, h3536, hc01, hc14, hlam, hphi, p3553_1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [hlam, p3553_0]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h2842, hlam, p3553_0]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h3202, hlam, p3553_1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h3396, hlam, p3553_0]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h2842, h3535, hc01, hlam, hphi, ht12, ht23, p3553_1, u3elo1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h2842, h3535, hc02, hlam, hphi, ht23, p3553_1, u3elo1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [hlam, p3553_0]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h0, h2842, h3202, h3535, hc01, hlam, hphi, ht12, ht23, p3553_1, u3elo1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h2842, h3535, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3553_1, u3elo1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h2282, h3539, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3553_1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h0, h3202, h3536, h3539, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3553_1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h3463, hlam, p3553_0]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [hlam, p3553_0]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h3465, hlam, p3553_0]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h2613, h3538, hc01, hlam, hphi, ht12, ht23, p3553_1, u3elo1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h0, h3396, h3535, h3548, hc01, hlam, hphi, ht12, ht23, p3553_1, u3elo1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h3464, hlam, p3553_0]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [h3396, h3535, h3548, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3553_1, u3elo1]
                                · have p3553_0 := h3553c.1
                                  have p3553_1 := h3553c.2.1
                                  have p3553_2 := h3553c.2.2.1
                                  have p3553_3 := h3553c.2.2.2
                                  linarith only [hlam, p3553_0]
                          · linarith only [h0, h2842, h3548, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h2842, h3547, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2842, h3464, h3535, h3538, hlam]
                  · linarith only [h0, h2842, h3535, h3537, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2842, h3535, h3536, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3535, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3585 | h3585
            · linarith only [h3463, h3464, h3585, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3587 | h3587
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3588 | h3588
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3589 | h3589
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3590 | h3590
                    · linarith only [h3463, h3464, h3590, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h1662, h3590, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h2842, h3587, h3589, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2842, h3587, h3588, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3587, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3596 | h3596
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3597 | h3597
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3598 | h3598
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3599 | h3599
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3600 | h3600
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3601 | h3601
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3602 | h3602
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3603 | h3603
                        · linarith only [h0, h3396, h3463, h3596, h3598, h3603, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h0, h2842, h3603, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h2282, h3597, h3602, hlam]
                    · linarith only [h3596, h3601, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h2842, h3598, h3600, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2842, h3598, h3599, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3598, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h3463, h3596, h3597, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3612 | h3612
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3613 | h3613
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3614 | h3614
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3615 | h3615
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3616 | h3616
                    · linarith only [h3596, h3616, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1662, h3616, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h2842, h3613, h3615, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2842, h3613, h3614, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3613, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3622 | h3622
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3623 | h3623
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3624 | h3624
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3625 | h3625
                    · linarith only [h0, h2842, h3596, h3625, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1662, h3625, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h2842, h3622, h3624, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2842, h3622, h3623, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3622, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1662 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2282 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2613 | h2613
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h1662 h2282 h2613
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h1662 h2282 h2613

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1662 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2282 | h2282
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h1662 h2282
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h1662 h2282

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1662 | h1662
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x0 m hb0 hb2 hb3 hb5 h0 h1662
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x1 m hb0 hb2 hb3 hb5 h0 h1662

end R2N4
