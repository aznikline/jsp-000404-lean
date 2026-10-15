import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3548000 in
set_option maxHeartbeats 3548000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_R_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h843 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h844 | h844
  · rcases m.htr 0 1 5 (by decide) (by decide) with h845 | h845
    · rcases m.htr 0 2 3 (by decide) (by decide) with h846 | h846
      · rcases m.htr 0 2 4 (by decide) (by decide) with h847 | h847
        · rcases m.htr 0 2 5 (by decide) (by decide) with h848 | h848
          · rcases m.htr 0 3 4 (by decide) (by decide) with h849 | h849
            · rcases m.htr 0 3 5 (by decide) (by decide) with h850 | h850
              · rcases m.htr 0 4 5 (by decide) (by decide) with h851 | h851
                · rcases m.htr 1 3 4 (by decide) (by decide) with h852 | h852
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h853 | h853
                    · linarith only [h0, h843, h852, h853, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h855 | h855
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h856 | h856
                        · linarith only [h852, h853, h856, hlam]
                        · rcases h0bigk with h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c | h858c
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [hlam, p858_0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h0, hlam, p858_1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h0, h849, h851, h852, h853, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p858_1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h0, h851, h852, h853, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p858_1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p858_1, u5ehi0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h843, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p858_1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [hlam, p858_0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h0, h849, h851, h852, h853, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p858_1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h0, h851, h852, h853, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p858_1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h0, h845, hc12, hlam, hphi, ht01, ht0b, ht5b, p858_1, u5ehi1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h843, hlam, p858_1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h846, hlam, p858_1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [hlam, p858_0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h851, h852, h853, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p858_1, u3elo0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h845, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p858_1, u3elo0, u5ehi1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h844, hlam, p858_0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h847, hlam, p858_0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h849, hlam, p858_0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [hlam, p858_0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h845, hc04, hlam, hphi, ht0b, ht5b, p858_1, u5ehi1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h845, hlam, p858_0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h848, hlam, p858_1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h850, hlam, p858_0]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [h851, hlam, p858_1]
                          · have p858_0 := h858c.1
                            have p858_1 := h858c.2.1
                            have p858_2 := h858c.2.2.1
                            have p858_3 := h858c.2.2.2
                            linarith only [hlam, p858_0]
                      · linarith only [h852, h855, hc23, hlam, hphi, u3elo1]
                  · linarith only [h849, h852, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h886 | h886
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h887 | h887
                    · linarith only [h0, h843, h851, h886, h887, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h889 | h889
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h890 | h890
                        · linarith only [h844, h851, h886, h890, hlam]
                        · rcases h0bigk with h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h0, hlam, p892_1]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h0, h850, hc12, hlam, hphi, ht01, ht0b, ht5b, p892_1, u5ehi3]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h0, h844, h886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p892_1]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h0, h848, hc12, hlam, hphi, ht01, ht0b, ht5b, p892_1, u5ehi2]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p892_1]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h0, h850, hc12, hlam, hphi, ht01, ht0b, ht5b, p892_1, u5ehi3]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            rcases p892_3 (m.d 0 1) (by simp) with h901 | h901
                            · linarith only [h0, h901, hlam]
                            · linarith only [h844, h901, hlam]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h0, h848, hc12, hlam, hphi, ht01, ht0b, ht5b, p892_1, u5ehi2]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h843, hlam, p892_1]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h846, hlam, p892_1]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h844, h886, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p892_1, u3elo0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h848, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p892_1, u3elo0, u5ehi2]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h844, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h847, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h849, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h851, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h845, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h848, hlam, p892_1]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h850, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h0, h844, h845, h886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p892_1]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [hlam, p892_0]
                      · linarith only [h886, h889, hc23, hlam, hphi, u3elo1]
                  · linarith only [h849, h886, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h922 | h922
                · linarith only [h849, h850, h922, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h924 | h924
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h925 | h925
                    · linarith only [h0, h843, h922, h924, h925, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h927 | h927
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h928 | h928
                        · linarith only [h849, h850, h922, h928, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · rcases h0bigk with h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c | h930c
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [hlam, p930_0]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h0, hlam, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h0, h844, h924, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p930_1, u5ehi0]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [hlam, p930_0]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h0, h849, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            rcases p930_3 (m.d 0 1) (by simp) with h939 | h939
                            · linarith only [h0, h939, hlam]
                            · linarith only [h844, h939, hlam]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h0, h843, h850, h924, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h843, hlam, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h846, hlam, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [hlam, p930_0]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h844, h850, h924, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p930_1, u3elo4]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h850, hlam, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h844, hlam, p930_0]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h847, hlam, p930_0]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h849, hlam, p930_0]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [hlam, p930_0]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h922, hlam, p930_0]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h845, hlam, p930_0]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h848, hlam, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h843, h924, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [h0, h844, h845, h924, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p930_1]
                          · have p930_0 := h930c.1
                            have p930_1 := h930c.2.1
                            have p930_2 := h930c.2.2.1
                            have p930_3 := h930c.2.2.2
                            linarith only [hlam, p930_0]
                      · linarith only [h843, h924, h927, hc23, hlam, hphi, u3elo0]
                  · linarith only [h849, h850, h924, hc13, hlam, hphi, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h960 | h960
              · linarith only [h849, h960, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h962 | h962
                · rcases m.htr 1 3 4 (by decide) (by decide) with h963 | h963
                  · linarith only [h849, h963, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h965 | h965
                    · linarith only [h0, h844, h965, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h849, h962, h963, h965, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h968 | h968
                  · linarith only [h843, h849, h968, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h970 | h970
                    · linarith only [h0, h844, h962, h970, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h972 | h972
                      · linarith only [h849, h972, hc03, hlam, hphi, u3elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h974 | h974
                        · linarith only [h843, h849, h962, h974, hc13, hlam, hphi, u3elo3]
                        · rcases h0bigk with h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [hlam, p976_0]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h0, hlam, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h0, h843, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h0, h843, h849, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h0, h845, hc12, hlam, hphi, ht01, ht0b, ht5b, p976_1, u5ehi1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [hlam, p976_0]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            rcases p976_3 (m.d 0 1) (by simp) with h984 | h984
                            · linarith only [h0, h984, hlam]
                            · linarith only [h843, h984, hlam]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            rcases p976_3 (m.d 0 1) (by simp) with h987 | h987
                            · linarith only [h0, h987, hlam]
                            · linarith only [h844, h987, hlam]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h0, h845, hc12, hlam, hphi, ht01, ht0b, ht5b, p976_1, u5ehi1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h843, hlam, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h846, hlam, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [hlam, p976_0]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h849, hlam, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h960, hlam, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h844, hlam, p976_0]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h847, hlam, p976_0]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h0, h843, h844, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [hlam, p976_0]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h962, hlam, p976_0]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h845, hlam, p976_0]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h848, hlam, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h0, h843, h845, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p976_1]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [h960, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p976_1, u3elo4]
                          · have p976_0 := h976c.1
                            have p976_1 := h976c.2.1
                            have p976_2 := h976c.2.2.1
                            have p976_3 := h976c.2.2.2
                            linarith only [hlam, p976_0]
          · linarith only [h0, h845, h848, hlam]
        · linarith only [h0, h844, h847, hlam]
      · linarith only [h0, h843, h846, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1009 | h1009
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1010 | h1010
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1011 | h1011
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1012 | h1012
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1013 | h1013
              · linarith only [h1013, h843, h845, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1015 | h1015
                · linarith only [h1012, h1013, h1015, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1017 | h1017
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1018 | h1018
                    · linarith only [h1015, h1018, h844, h845, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h1017, h1018, h843, h845, hc34, hc45, hlam, hphi]
                  · linarith only [h1012, h1013, h1017, hc13, hlam, hphi, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1022 | h1022
              · linarith only [h1012, h1022, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1024 | h1024
                · linarith only [h1024, h844, h845, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1026 | h1026
                  · linarith only [h1012, h1026, h843, h845, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1028 | h1028
                    · linarith only [h0, h1028, h844, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1030 | h1030
                      · linarith only [h1009, h1012, h1030, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1032 | h1032
                        · linarith only [h1028, h1032, h845, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases h0bigk with h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h845, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            rcases p1034_3 (m.d 0 1) (by simp) with h1042 | h1042
                            · linarith only [h0, h1042, hlam]
                            · linarith only [h1042, h843, hlam]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            rcases p1034_3 (m.d 0 1) (by simp) with h1045 | h1045
                            · linarith only [h0, h1045, hlam]
                            · linarith only [h1045, h844, hlam]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1034_1, u5ehi0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h843, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1009, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1012, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1022, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h844, hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1010, hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1009, h844, h845, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1024, hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h843, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1011, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1009, h1022, hc23, hlam, hphi, p1034_1, u3elo4]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1022, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1034_1, u3elo4]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [hlam, p1034_0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1064 | h1064
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1065 | h1065
              · linarith only [h1065, h843, h845, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1067 | h1067
                · linarith only [h1064, h1065, h1067, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1069 | h1069
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1070 | h1070
                    · linarith only [h0, h1067, h1069, h1070, h843, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h1069, h1070, h843, h845, hc34, hc45, hlam, hphi]
                  · linarith only [h1064, h1065, h1069, hc13, hlam, hphi, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1074 | h1074
              · linarith only [h1064, h1074, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1076 | h1076
                · linarith only [h0, h1011, h1076, h844, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1078 | h1078
                  · linarith only [h1064, h1078, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1080 | h1080
                    · linarith only [h0, h1011, h1074, h1076, h1080, h844, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1082 | h1082
                      · linarith only [h1064, h1082, h843, hc13, hlam, hphi, u3elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1084 | h1084
                        · linarith only [h1080, h1084, h845, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases h0bigk with h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [hlam, p1086_0]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h0, hlam, p1086_1]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h843, h845, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1086_1]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h0, h1011, h1064, h1074, h843, hc13, hlam, hphi, p1086_1, u3elo4]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h845, hlam, p1086_1]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1011, h1074, hc01, hlam, hphi, ht12, ht23, p1086_1, u3elo4]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [hlam, p1086_0]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1011, h1074, h843, hc13, hlam, hphi, p1086_1, u3elo4]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1011, h1064, h1074, h843, hc13, hlam, hphi, p1086_1, u3elo4]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1011, hlam, p1086_0]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h843, hlam, p1086_1]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1009, hlam, p1086_1]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [hlam, p1086_0]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1064, hlam, p1086_1]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1074, hlam, p1086_1]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h844, hlam, p1086_0]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1010, hlam, p1086_0]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h0, h843, h844, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1086_1]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [hlam, p1086_0]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1076, hlam, p1086_0]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1074, hc01, hlam, hphi, ht12, ht23, p1086_1, u3elo4]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1074, hc02, hlam, hphi, ht23, p1086_1, u3elo4]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1074, h843, hc13, hlam, hphi, p1086_1, u3elo4]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [h1074, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1086_1, u3elo4]
                          · have p1086_0 := h1086c.1
                            have p1086_1 := h1086c.2.1
                            have p1086_2 := h1086c.2.2.1
                            have p1086_3 := h1086c.2.2.2
                            linarith only [hlam, p1086_0]
        · linarith only [h0, h1010, h844, hlam]
      · linarith only [h0, h1009, h843, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1114 | h1114
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1115 | h1115
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1116 | h1116
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1117 | h1117
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1118 | h1118
            · linarith only [h1118, h843, h844, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1120 | h1120
              · linarith only [h1118, h1120, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1122 | h1122
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1123 | h1123
                  · linarith only [h1118, h1123, h843, h844, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1123, h843, h844, hc13, hlam, hphi, u3elo3]
                · linarith only [h1114, h1122, h844, hlam]
          · linarith only [h1114, h1116, h1117, h844, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1128 | h1128
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1129 | h1129
            · linarith only [h0, h1116, h1129, h843, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1131 | h1131
              · linarith only [h1129, h1131, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1133 | h1133
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1134 | h1134
                  · linarith only [h1129, h1134, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1134, h843, h844, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h1114, h1116, h1133, hlam]
          · linarith only [h0, h1114, h1128, hlam]
      · linarith only [h0, h1115, h843, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1140 | h1140
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1141 | h1141
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1142 | h1142
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1143 | h1143
            · linarith only [h1143, h843, h844, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1145 | h1145
              · linarith only [h1143, h1145, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1147 | h1147
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1148 | h1148
                  · linarith only [h1143, h1148, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1148, h843, h844, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1151 | h1151
                  · linarith only [h1147, h1151, h843, h844, hc34, hc45, hlam, hphi]
                  · linarith only [h1151, h843, h844, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1154 | h1154
            · linarith only [h1154, h843, h844, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1156 | h1156
              · linarith only [h1154, h1156, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1158 | h1158
                · linarith only [h1141, h1142, h1158, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1160 | h1160
                  · linarith only [h1154, h1160, h843, h844, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1160, h843, h844, hc13, hlam, hphi, u3elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1163 | h1163
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1164 | h1164
            · linarith only [h0, h1141, h1164, h843, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1166 | h1166
              · linarith only [h1164, h1166, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1168 | h1168
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1169 | h1169
                  · linarith only [h1164, h1169, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1169, h843, h844, hc13, hlam, hphi, u3elo3]
                · linarith only [h1141, h1163, h1168, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1173 | h1173
            · linarith only [h0, h1141, h1173, h843, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1175 | h1175
              · linarith only [h1173, h1175, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1177 | h1177
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1178 | h1178
                  · linarith only [h1173, h1178, h843, h844, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1178, h843, h844, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1181 | h1181
                  · linarith only [h0, h1141, h1177, h1181, h843, hc34, hc45, hlam, hphi]
                  · linarith only [h1181, h843, h844, hc13, hlam, hphi, u3elo3]
      · linarith only [h0, h1140, h843, hc13, hlam, hphi, u3elo2]

end R2N4
