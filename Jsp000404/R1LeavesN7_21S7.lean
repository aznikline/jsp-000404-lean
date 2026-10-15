import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4554 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4555 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 3 5 (by decide) (by decide) with h5849 | h5849
  · linarith only [h4553, h4555, h5849, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5851 | h5851
    · linarith only [h4554, h4555, h5851, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5853 | h5853
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5854 | h5854
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5855 | h5855
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5856 | h5856
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5857 | h5857
              · linarith only [h4553, h4555, h5855, h5857, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5859 | h5859
                · linarith only [h4554, h4555, h5849, h5855, h5857, h5859, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5861 | h5861
                  · linarith only [h4554, h4555, h5851, h5855, h5861, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5863 | h5863
                    · linarith only [h4554, h4555, h5857, h5861, h5863, hc23, hc34, hlam, hphi]
                    · rcases h2bigk with h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h0, hlam, p5865_1]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h4555, h5854, h5856, h5859, h5863, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5865_1]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h4555, h5854, h5856, h5859, h5863, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5865_1]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h4555, hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        rcases p5865_3 (m.d 0 2) (by simp) with h5871 | h5871
                        · linarith only [h0, h5871, hlam]
                        · rcases p5865_3 (m.d 1 2) (by simp) with h5873 | h5873
                          · rcases p5865_3 (m.d 2 3) (by simp) with h5874 | h5874
                            · linarith only [h5853, h5874, hlam]
                            · rcases p5865_3 (m.d 2 4) (by simp) with h5876 | h5876
                              · linarith only [h5854, h5876, hlam]
                              · rcases p5865_3 (m.d 2 5) (by simp) with h5878 | h5878
                                · linarith only [h5855, h5878, hlam]
                                · linarith only [h4555, h5878, hlam]
                          · linarith only [h0, h5873, hlam]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h4553, h4555, h5854, h5856, h5859, h5863, hlam, p5865_2]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h4554, h4555, h5854, h5856, h5859, h5863, hlam, p5865_2]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h4554, h4555, h5857, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5865_1]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h4553, hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h5853, hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h5857, hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h5859, hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h4554, hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h5854, hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h4554, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5865_1, u0elo1]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h5861, hlam, p5865_1]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h4554, h5855, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5865_1]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [h5855, hlam, p5865_0]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        rcases p5865_3 (m.d 0 2) (by simp) with h5898 | h5898
                        · linarith only [h4555, h5898, hlam]
                        · linarith only [h4553, h5898, hlam]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        rcases p5865_3 (m.d 0 2) (by simp) with h5901 | h5901
                        · linarith only [h4555, h5901, hlam]
                        · linarith only [h4554, h5901, hlam]
                      · have p5865_0 := h5865c.1
                        have p5865_1 := h5865c.2.1
                        have p5865_2 := h5865c.2.2.1
                        have p5865_3 := h5865c.2.2.2
                        linarith only [hlam, p5865_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5905 | h5905
              · linarith only [h4553, h4555, h5855, h5905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5907 | h5907
                · linarith only [h4554, h4555, h5849, h5855, h5905, h5907, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5909 | h5909
                  · linarith only [h4554, h4555, h5855, h5856, h5909, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5911 | h5911
                    · linarith only [h4554, h4555, h5855, h5856, h5905, h5911, hc23, hc34, hlam, hphi]
                    · rcases h2bigk with h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c | h5913c
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h0, hlam, p5913_1]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h4555, h5855, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5913_1]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h4555, h5855, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5913_1]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h4555, hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        rcases p5913_3 (m.d 0 2) (by simp) with h5919 | h5919
                        · linarith only [h0, h5919, hlam]
                        · rcases p5913_3 (m.d 1 2) (by simp) with h5921 | h5921
                          · rcases p5913_3 (m.d 2 3) (by simp) with h5922 | h5922
                            · linarith only [h5853, h5922, hlam]
                            · rcases p5913_3 (m.d 2 4) (by simp) with h5924 | h5924
                              · linarith only [h5854, h5924, hlam]
                              · rcases p5913_3 (m.d 2 5) (by simp) with h5926 | h5926
                                · linarith only [h5855, h5926, hlam]
                                · linarith only [h4555, h5926, hlam]
                          · linarith only [h0, h5921, hlam]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h4553, h4555, h5855, hlam, p5913_2]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h4554, h4555, h5855, hlam, p5913_2]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h4554, h4555, h5905, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5913_1]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h4553, hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h5853, hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h5905, hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h5907, hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h4554, hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h5854, hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h4554, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5913_1, u0elo1]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h5909, hlam, p5913_1]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h4553, h5907, hc23, hc35, hlam, hphi, p5913_1]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [h5855, hlam, p5913_0]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        rcases p5913_3 (m.d 0 2) (by simp) with h5946 | h5946
                        · linarith only [h4555, h5946, hlam]
                        · linarith only [h4553, h5946, hlam]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        rcases p5913_3 (m.d 0 2) (by simp) with h5949 | h5949
                        · linarith only [h4555, h5949, hlam]
                        · linarith only [h4554, h5949, hlam]
                      · have p5913_0 := h5913c.1
                        have p5913_1 := h5913c.2.1
                        have p5913_2 := h5913c.2.2.1
                        have p5913_3 := h5913c.2.2.2
                        linarith only [hlam, p5913_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5953 | h5953
            · linarith only [h5854, h5855, h5953, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5955 | h5955
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5956 | h5956
                · linarith only [h4553, h5849, h5956, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5958 | h5958
                  · linarith only [h0, h4553, h4554, h5855, h5953, h5955, h5958, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h4553, h4555, h5955, h5958, hc34, hc45, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5961 | h5961
                · linarith only [h4553, h5849, h5961, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5963 | h5963
                  · linarith only [h4554, h5851, h5963, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5965 | h5965
                    · linarith only [h0, h5855, h5963, h5965, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases h2bigk with h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c | h5967c
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h0, hlam, p5967_1]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h0, h5855, h5961, hc23, hc35, hlam, hphi, p5967_1]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h0, h5855, h5955, h5961, h5965, hc23, hc45, hlam, hphi, ht34, p5967_1]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h4555, hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h5855, h5961, h5965, hc02, hc45, hlam, hphi, ht23, ht34, p5967_1]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h5855, h5961, h5965, hc23, hc45, hlam, hphi, ht34, p5967_1]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h5855, h5955, h5961, h5965, hc23, hc45, hlam, hphi, ht34, p5967_1]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h5855, hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h4553, hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h5853, hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h5955, hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h5961, hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h4554, hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h5854, hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h4554, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5967_1, u0elo1]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [hlam, p5967_0]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h5963, hlam, p5967_1]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h4554, h5961, h5965, hc24, hc45, hlam, hphi, p5967_1]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [h0, h5961, h5965, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5967_1]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        rcases p5967_3 (m.d 0 2) (by simp) with h5990 | h5990
                        · linarith only [h4555, h5990, hlam]
                        · linarith only [h4553, h5990, hlam]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        rcases p5967_3 (m.d 0 2) (by simp) with h5993 | h5993
                        · linarith only [h4555, h5993, hlam]
                        · linarith only [h4554, h5993, hlam]
                      · have p5967_0 := h5967c.1
                        have p5967_1 := h5967c.2.1
                        have p5967_2 := h5967c.2.2.1
                        have p5967_3 := h5967c.2.2.2
                        linarith only [hlam, p5967_0]
        · linarith only [h0, h4554, h5854, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h4553, h5853, hlam]

set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4554 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 2 5 (by decide) (by decide) with h4555 | h4555
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x0 m hb0 hb2 hb5 hg0 hg2858 h4553 h4554 h4555
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x1 m hb0 hb2 hb5 hg0 hg2858 h4553 h4554 h4555

set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4554 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 2 5 (by decide) (by decide) with h5999 | h5999
  · rcases m.htr 0 3 5 (by decide) (by decide) with h6000 | h6000
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6001 | h6001
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6002 | h6002
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6003 | h6003
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6004 | h6004
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6005 | h6005
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6006 | h6006
                · linarith only [h4553, h4554, h6003, h6006, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6008 | h6008
                  · linarith only [h4553, h4554, h6003, h6008, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h4553, h4554, h6000, h6003, h6008, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h4554, h6001, h6003, h6005, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
            · linarith only [h4553, h4554, h6003, h6004, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6013 | h6013
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6014 | h6014
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6015 | h6015
                · linarith only [h0, h4553, h6003, h6015, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6017 | h6017
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6018 | h6018
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6019 | h6019
                      · rcases h2bigk with h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c | h6020c
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h0, hlam, p6020_1]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h0, h6003, h6015, h6017, h6019, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6020_1]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h4554, hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          rcases p6020_3 (m.d 0 2) (by simp) with h6025 | h6025
                          · rcases p6020_3 (m.d 1 2) (by simp) with h6026 | h6026
                            · rcases p6020_3 (m.d 2 3) (by simp) with h6027 | h6027
                              · linarith only [h4553, h6027, hlam]
                              · linarith only [h6017, h6027, hlam]
                            · linarith only [h6013, h6026, hlam]
                          · linarith only [h6025, hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h6003, h6015, hc02, hc34, hlam, hphi, ht23, p6020_1]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h6003, h6015, h6017, h6019, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6020_1]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h6003, hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          rcases p6020_3 (m.d 0 2) (by simp) with h6036 | h6036
                          · linarith only [h0, h6036, hlam]
                          · linarith only [h5999, h6036, hlam]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h4553, hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h6002, hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h6015, hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h4553, h6017, h6019, hc45, hlam, hphi, ht0b, ht5b, p6020_1, u0elo1]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h4553, h6015, hc23, hc34, hlam, hphi, p6020_1]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h0, h6015, hc01, hc34, hlam, hphi, ht12, ht23, p6020_1]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          rcases p6020_3 (m.d 0 2) (by simp) with h6046 | h6046
                          · linarith only [h4554, h6046, hlam]
                          · linarith only [h4553, h6046, hlam]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          rcases p6020_3 (m.d 0 2) (by simp) with h6050 | h6050
                          · linarith only [h4554, h6050, hlam]
                          · linarith only [h5999, h6050, hlam]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h5999, hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h6013, hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h6017, hlam, p6020_1]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [h6018, hlam, p6020_0]
                        · have p6020_0 := h6020c.1
                          have p6020_1 := h6020c.2.1
                          have p6020_2 := h6020c.2.2.1
                          have p6020_3 := h6020c.2.2.2
                          linarith only [hlam, p6020_0]
                      · linarith only [h6001, h6015, h6017, h6019, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                    · linarith only [h0, h6001, h6003, h6018, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h4553, h6000, h6003, h6015, h6017, hc23, hc34, hlam, hphi]
              · linarith only [h0, h5999, h6001, h6003, h6014, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
            · linarith only [h0, h5999, h6013, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h4553, h6002, hlam]
      · linarith only [h4553, h4554, h6000, h6001, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6065 | h6065
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6066 | h6066
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6067 | h6067
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6068 | h6068
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6069 | h6069
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6070 | h6070
                · linarith only [h4553, h4554, h6067, h6070, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6072 | h6072
                  · linarith only [h4553, h4554, h6000, h6067, h6072, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6074 | h6074
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6075 | h6075
                      · rcases h2bigk with h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h0, hlam, p6076_1]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h4554, h6067, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6076_1]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h4554, hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h4554, h6067, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6076_1]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          rcases p6076_3 (m.d 0 2) (by simp) with h6082 | h6082
                          · linarith only [h0, h6082, hlam]
                          · rcases p6076_3 (m.d 1 2) (by simp) with h6084 | h6084
                            · rcases p6076_3 (m.d 2 3) (by simp) with h6085 | h6085
                              · linarith only [h6066, h6085, hlam]
                              · rcases p6076_3 (m.d 2 4) (by simp) with h6087 | h6087
                                · linarith only [h6067, h6087, hlam]
                                · linarith only [h4554, h6087, hlam]
                            · linarith only [h0, h6084, hlam]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h4553, h4554, h6067, hlam, p6076_2]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h0, h4554, hc01, hc12, hlam, hphi, p6076_1]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h4554, h5999, h6067, hlam, p6076_2]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h4553, hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h6066, hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h6070, hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h6072, hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h5999, h6070, h6072, hc23, hc34, hlam, hphi, p6076_1]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h6067, hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          rcases p6076_3 (m.d 0 2) (by simp) with h6102 | h6102
                          · linarith only [h4554, h6102, hlam]
                          · linarith only [h4553, h6102, hlam]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          rcases p6076_3 (m.d 0 2) (by simp) with h6106 | h6106
                          · linarith only [h4554, h6106, hlam]
                          · linarith only [h5999, h6106, hlam]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h5999, hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h6068, hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h5999, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6076_1, u0elo1]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [h6074, hlam, p6076_0]
                        · have p6076_0 := h6076c.1
                          have p6076_1 := h6076c.2.1
                          have p6076_2 := h6076c.2.2.1
                          have p6076_3 := h6076c.2.2.2
                          linarith only [hlam, p6076_0]
                      · linarith only [h4554, h5999, h6065, h6067, h6070, h6075, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h4554, h5999, h6065, h6074, hlam]
              · linarith only [h4554, h5999, h6065, h6067, h6069, hlam]
            · linarith only [h4554, h5999, h6067, h6068, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6118 | h6118
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6119 | h6119
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6120 | h6120
                · linarith only [h0, h4553, h6067, h6120, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6122 | h6122
                  · linarith only [h4553, h6000, h6122, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6124 | h6124
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6125 | h6125
                      · rcases h2bigk with h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c | h6126c
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h0, hlam, p6126_1]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h0, h6067, h6120, hc23, hc34, hlam, hphi, p6126_1]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h4554, hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h0, h6067, h6120, h6122, hc23, hc34, hlam, hphi, p6126_1]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h6067, h6120, hc02, hc34, hlam, hphi, ht23, p6126_1]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h6067, h6120, hc23, hc34, hlam, hphi, p6126_1]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h6067, hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h6067, h6120, h6122, hc23, hc34, hlam, hphi, p6126_1]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h4553, hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h6066, hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h6120, hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h6122, hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h5999, h6120, h6122, hc23, hc34, hlam, hphi, p6126_1]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h0, h6120, hc01, hc34, hlam, hphi, ht12, ht23, p6126_1]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          rcases p6126_3 (m.d 0 2) (by simp) with h6144 | h6144
                          · linarith only [h4554, h6144, hlam]
                          · linarith only [h4553, h6144, hlam]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          rcases p6126_3 (m.d 0 2) (by simp) with h6148 | h6148
                          · linarith only [h4554, h6148, hlam]
                          · linarith only [h5999, h6148, hlam]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h5999, hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h6118, hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h5999, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6126_1, u0elo1]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [h6124, hlam, p6126_0]
                        · have p6126_0 := h6126c.1
                          have p6126_1 := h6126c.2.1
                          have p6126_2 := h6126c.2.2.1
                          have p6126_3 := h6126c.2.2.2
                          linarith only [hlam, p6126_0]
                      · linarith only [h0, h6067, h6120, h6125, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h2858, h6065, h6067, h6118, h6124, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
              · linarith only [h0, h5999, h6065, h6067, h6119, hlam]
            · linarith only [h0, h5999, h6118, hlam]
        · linarith only [h0, h4553, h6066, hlam]
      · linarith only [h4554, h5999, h6065, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h6162 | h6162
    · linarith only [h4553, h5999, h6162, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6164 | h6164
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6165 | h6165
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6166 | h6166
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6167 | h6167
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6168 | h6168
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6169 | h6169
                · linarith only [h4553, h4554, h6166, h6169, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6171 | h6171
                  · linarith only [h4553, h4554, h6162, h6166, h6171, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6173 | h6173
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6174 | h6174
                      · rcases h2bigk with h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c | h6175c
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h0, hlam, p6175_1]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h5999, h6166, h6173, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6175_1]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h4554, hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h5999, hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          rcases p6175_3 (m.d 0 2) (by simp) with h6181 | h6181
                          · linarith only [h0, h6181, hlam]
                          · rcases p6175_3 (m.d 1 2) (by simp) with h6183 | h6183
                            · rcases p6175_3 (m.d 2 3) (by simp) with h6184 | h6184
                              · linarith only [h6165, h6184, hlam]
                              · rcases p6175_3 (m.d 2 4) (by simp) with h6186 | h6186
                                · linarith only [h6166, h6186, hlam]
                                · linarith only [h4554, h6186, hlam]
                            · linarith only [h0, h6183, hlam]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h4553, h5999, h6166, h6173, hlam, p6175_2]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h0, h5999, h6173, hc01, hc12, hlam, hphi, p6175_1]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h4553, h5999, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6175_1]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h4553, hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h6165, hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h6169, hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h6171, hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h4553, h6169, hc23, hc34, hlam, hphi, p6175_1]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h6166, hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          rcases p6175_3 (m.d 0 2) (by simp) with h6201 | h6201
                          · linarith only [h4554, h6201, hlam]
                          · linarith only [h4553, h6201, hlam]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h4553, h5999, h6166, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6175_1]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h4553, h6171, hc23, hc35, hlam, hphi, p6175_1]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h6167, hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          rcases p6175_3 (m.d 0 2) (by simp) with h6208 | h6208
                          · linarith only [h5999, h6208, hlam]
                          · linarith only [h4553, h6208, hlam]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [h6173, hlam, p6175_0]
                        · have p6175_0 := h6175c.1
                          have p6175_1 := h6175c.2.1
                          have p6175_2 := h6175c.2.2.1
                          have p6175_3 := h6175c.2.2.2
                          linarith only [hlam, p6175_0]
                      · linarith only [h6164, h6169, h6174, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h4553, h4554, h6164, h6173, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
              · linarith only [h4554, h6164, h6166, h6168, hlam]
            · linarith only [h4553, h4554, h6166, h6167, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6217 | h6217
            · linarith only [h4553, h5999, h6166, h6217, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6219 | h6219
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6220 | h6220
                · linarith only [h0, h4553, h5999, h6164, h6166, h6220, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6222 | h6222
                  · linarith only [h4553, h6162, h6222, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6224 | h6224
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6225 | h6225
                      · rcases h2bigk with h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c | h6226c
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h0, hlam, p6226_1]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h0, h6217, h6220, h6224, hc23, hc34, hlam, hphi, p6226_1]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h4554, hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h5999, hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h6217, h6224, hc02, hc24, hlam, hphi, p6226_1]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h6217, h6220, h6224, hc23, hc34, hlam, hphi, p6226_1]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h6166, hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h6217, hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h4553, hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h6165, hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h6220, hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h6222, hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h4553, h6220, hc23, hc34, hlam, hphi, p6226_1]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h0, h6220, hc01, hc34, hlam, hphi, ht12, ht23, p6226_1]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          rcases p6226_3 (m.d 0 2) (by simp) with h6244 | h6244
                          · linarith only [h4554, h6244, hlam]
                          · linarith only [h4553, h6244, hlam]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h4553, h5999, h6220, hc23, hc34, hlam, hphi, p6226_1]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h4553, h6222, hc23, hc35, hlam, hphi, p6226_1]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h0, h6222, hc01, hc35, hlam, hphi, ht12, ht23, p6226_1]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          rcases p6226_3 (m.d 0 2) (by simp) with h6251 | h6251
                          · linarith only [h5999, h6251, hlam]
                          · linarith only [h4553, h6251, hlam]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [h6224, hlam, p6226_0]
                        · have p6226_0 := h6226c.1
                          have p6226_1 := h6226c.2.1
                          have p6226_2 := h6226c.2.2.1
                          have p6226_3 := h6226c.2.2.2
                          linarith only [hlam, p6226_0]
                      · linarith only [h4553, h4554, h6220, h6225, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h2858, h6164, h6166, h6219, h6224, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h0, h6164, h6166, h6219, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
        · linarith only [h0, h4553, h6165, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6260 | h6260
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6261 | h6261
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6262 | h6262
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6263 | h6263
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6264 | h6264
                · linarith only [h4553, h4554, h6164, h6261, h6263, h6264, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6266 | h6266
                  · linarith only [h4553, h4554, h6164, h6261, h6263, h6266, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6268 | h6268
                    · linarith only [h4553, h4554, h6164, h6261, h6268, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h4553, h4554, h6268, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h4553, h4554, h6261, h6263, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4553, h4554, h6261, h6262, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6273 | h6273
            · linarith only [h4553, h5999, h6261, h6273, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6275 | h6275
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6276 | h6276
                · linarith only [h4553, h4554, h6164, h6261, h6275, h6276, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h4553, h4554, h6164, h6261, h6275, h6276, hc23, hc34, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6279 | h6279
                · linarith only [h0, h4553, h6261, h6275, h6279, hc34, hc45, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6281 | h6281
                  · linarith only [h0, h2858, h4553, h6162, h6261, h6275, h6281, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6283 | h6283
                    · linarith only [h0, h4553, h6261, h6275, h6279, h6283, hc23, hc34, hlam, hphi]
                    · linarith only [h4553, h4554, h6283, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h0, h4553, h6260, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]

set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 2 4 (by decide) (by decide) with h4554 | h4554
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0 m hb0 hb2 hb5 hg0 hg2858 h4553 h4554
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x1 m hb0 hb2 hb5 hg0 hg2858 h4553 h4554

end R2N4
