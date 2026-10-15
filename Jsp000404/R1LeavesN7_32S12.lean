import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S10
import Jsp000404.R1LeavesN7_32S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2630 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2631 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h2632 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2633 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2634 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 2 3 4 (by decide) (by decide) with h3050 | h3050
  · rcases m.htr 2 3 5 (by decide) (by decide) with h3051 | h3051
    · rcases m.htr 2 4 5 (by decide) (by decide) with h3052 | h3052
      · linarith only [h0, h1407, h2009, h2634, h3050, h3052, hc01, hc12, hlam, hphi]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3054 | h3054
        · linarith only [h0, h1407, h2010, h2634, h3050, h3054, hc01, hc12, hlam, hphi]
        · rcases h2bigk with h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h0, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            rcases p3056_3 (m.d 0 2) (by simp) with h3059 | h3059
            · rcases p3056_3 (m.d 1 2) (by simp) with h3060 | h3060
              · rcases p3056_3 (m.d 2 3) (by simp) with h3061 | h3061
                · linarith only [h3061, hlam, p3056_0]
                · rcases p3056_3 (m.d 2 4) (by simp) with h3063 | h3063
                  · linarith only [h2010, h3063, hlam]
                  · rcases p3056_3 (m.d 2 5) (by simp) with h3065 | h3065
                    · linarith only [h2011, h3065, hlam]
                    · rcases h3bigk with h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h879, hlam, p3067_1]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        rcases p3067_3 (m.d 0 3) (by simp) with h3070 | h3070
                        · rcases p3067_3 (m.d 1 3) (by simp) with h3071 | h3071
                          · rcases p3067_3 (m.d 2 3) (by simp) with h3072 | h3072
                            · linarith only [h2009, h3072, hlam]
                            · rcases p3067_3 (m.d 3 4) (by simp) with h3074 | h3074
                              · linarith only [h2012, h3074, hlam]
                              · rcases p3067_3 (m.d 3 5) (by simp) with h3076 | h3076
                                · linarith only [h2013, h3076, hlam]
                                · rcases h3emax with h3078 | h3078 | h3078 | h3078 | h3078
                                  · linarith only [h3078, hc23, hlam, p3067_1]
                                  · linarith only [h3078, h879, hc01, hlam, ht12, ht23]
                                  · linarith only [h3078, hlam, ht23, u2ehi2]
                                  · rcases h5bigk with h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c | h3082c
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [hlam, p3082_0]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h1407, hlam, p3082_1]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h2014, h3052, hc45, hlam, hphi, ht23, ht34, p3082_1, u2ehi3]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      rcases p3082_3 (m.d 0 5) (by simp) with h3086 | h3086
                                      · rcases p3082_3 (m.d 1 5) (by simp) with h3087 | h3087
                                        · rcases p3082_3 (m.d 2 5) (by simp) with h3088 | h3088
                                          · linarith only [h2011, h3088, hlam]
                                          · linarith only [h3051, h3088, hlam]
                                        · linarith only [h2633, h3087, hlam]
                                      · linarith only [h2013, h3086, hlam]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h2014, hlam, p3082_0]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h2011, h2634, h3052, hc45, hlam, hphi, ht23, ht34, p3082_1, u2ehi3]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [hlam, p3082_0]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h2634, h3052, hc45, hlam, hphi, ht23, ht34, p3082_1, u2ehi3]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      rcases p3082_3 (m.d 0 5) (by simp) with h3097 | h3097
                                      · linarith only [h1407, h3097, hlam]
                                      · linarith only [h2013, h3097, hlam]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h2634, hlam, p3082_0]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h2011, hlam, p3082_1]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h2631, hlam, p3082_1]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [hlam, p3082_0]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h0, h2009, h3051, h3054, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3067_1, p3082_1]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h3052, hlam, p3082_0]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h2013, hlam, p3082_1]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h2633, hlam, p3082_1]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h3051, hlam, p3082_0]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [hlam, p3082_0]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h3054, hlam, p3082_0]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h2011, h3052, hc45, hlam, hphi, ht23, ht34, p3082_1, u2ehi3]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h0, h1407, h2009, h3051, h3052, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p3067_1, p3082_1, u2ehi3]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [h3052, hc45, hlam, hphi, ht23, ht34, p3082_1, u2ehi3]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      rcases p3082_3 (m.d 0 5) (by simp) with h3114 | h3114
                                      · linarith only [h2014, h3114, hlam]
                                      · linarith only [h2013, h3114, hlam]
                                    · have p3082_0 := h3082c.1
                                      have p3082_1 := h3082c.2.1
                                      have p3082_2 := h3082c.2.2.1
                                      have p3082_3 := h3082c.2.2.2
                                      linarith only [hlam, p3082_0]
                                  · rcases h5bigk with h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [hlam, p3118_0]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h1407, hlam, p3118_1]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h2014, h3052, hc45, hlam, hphi, ht23, ht34, p3118_1, u2ehi3]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      rcases p3118_3 (m.d 0 5) (by simp) with h3122 | h3122
                                      · rcases p3118_3 (m.d 1 5) (by simp) with h3123 | h3123
                                        · rcases p3118_3 (m.d 2 5) (by simp) with h3124 | h3124
                                          · linarith only [h2011, h3124, hlam]
                                          · linarith only [h3051, h3124, hlam]
                                        · linarith only [h2633, h3123, hlam]
                                      · linarith only [h2013, h3122, hlam]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h2014, hlam, p3118_0]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h2011, h2634, h3052, hc45, hlam, hphi, ht23, ht34, p3118_1, u2ehi3]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [hlam, p3118_0]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h2634, h3052, hc45, hlam, hphi, ht23, ht34, p3118_1, u2ehi3]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      rcases p3118_3 (m.d 0 5) (by simp) with h3133 | h3133
                                      · linarith only [h1407, h3133, hlam]
                                      · linarith only [h2013, h3133, hlam]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h2634, hlam, p3118_0]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h2011, hlam, p3118_1]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h2631, hlam, p3118_1]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [hlam, p3118_0]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h0, h2009, h3051, h3054, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3067_1, p3118_1]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h3052, hlam, p3118_0]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h2013, hlam, p3118_1]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h2633, hlam, p3118_1]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h3051, hlam, p3118_0]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [hlam, p3118_0]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h3054, hlam, p3118_0]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h2011, h3052, hc45, hlam, hphi, ht23, ht34, p3118_1, u2ehi3]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h0, h1407, h2009, h3051, h3052, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p3067_1, p3118_1, u2ehi3]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [h3052, hc45, hlam, hphi, ht23, ht34, p3118_1, u2ehi3]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      rcases p3118_3 (m.d 0 5) (by simp) with h3150 | h3150
                                      · linarith only [h2014, h3150, hlam]
                                      · linarith only [h2013, h3150, hlam]
                                    · have p3118_0 := h3118c.1
                                      have p3118_1 := h3118c.2.1
                                      have p3118_2 := h3118c.2.2.1
                                      have p3118_3 := h3118c.2.2.2
                                      linarith only [hlam, p3118_0]
                          · linarith only [h2629, h3071, hlam]
                        · linarith only [h2009, h3070, hlam]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        rcases p3067_3 (m.d 0 3) (by simp) with h3156 | h3156
                        · rcases p3067_3 (m.d 1 3) (by simp) with h3157 | h3157
                          · rcases p3067_3 (m.d 2 3) (by simp) with h3158 | h3158
                            · linarith only [h2009, h3158, hlam]
                            · linarith only [h3050, h3158, hlam]
                          · linarith only [h2632, h3157, hlam]
                        · linarith only [h3156, hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        rcases p3067_3 (m.d 0 3) (by simp) with h3163 | h3163
                        · rcases p3067_3 (m.d 1 3) (by simp) with h3164 | h3164
                          · rcases p3067_3 (m.d 2 3) (by simp) with h3165 | h3165
                            · linarith only [h2009, h3165, hlam]
                            · linarith only [h3051, h3165, hlam]
                          · linarith only [h2633, h3164, hlam]
                        · linarith only [h3163, hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        rcases p3067_3 (m.d 0 3) (by simp) with h3170 | h3170
                        · linarith only [h3170, h879, hlam]
                        · rcases p3067_3 (m.d 1 3) (by simp) with h3172 | h3172
                          · rcases p3067_3 (m.d 2 3) (by simp) with h3173 | h3173
                            · linarith only [h2629, h3173, hlam]
                            · rcases p3067_3 (m.d 3 4) (by simp) with h3175 | h3175
                              · linarith only [h2632, h3175, hlam]
                              · rcases p3067_3 (m.d 3 5) (by simp) with h3177 | h3177
                                · linarith only [h2633, h3177, hlam]
                                · rcases h3emax with h3179 | h3179 | h3179 | h3179 | h3179
                                  · linarith only [h2009, h3051, h3052, h3179, hlam, ht23, u2ehi3]
                                  · linarith only [h2009, h3051, h3052, h3179, hlam, ht23, p3067_1, u2ehi3]
                                  · linarith only [h3051, h3052, h3179, hlam, ht23, u2ehi3]
                                  · rcases h5bigk with h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [hlam, p3183_0]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h1407, hlam, p3183_1]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2013, h2629, h3052, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3067_1, p3183_1, u2ehi3]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2013, h2629, h3054, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3067_1, p3183_1]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2014, hlam, p3183_0]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2011, h2634, h3052, hc45, hlam, hphi, ht23, ht34, p3183_1, u2ehi3]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [hlam, p3183_0]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2634, h3052, hc45, hlam, hphi, ht23, ht34, p3183_1, u2ehi3]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      rcases p3183_3 (m.d 0 5) (by simp) with h3192 | h3192
                                      · linarith only [h1407, h3192, hlam]
                                      · linarith only [h2013, h3192, hlam]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2634, hlam, p3183_0]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2011, hlam, p3183_1]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2631, hlam, p3183_1]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [hlam, p3183_0]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h3051, h3054, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3056_1, p3183_1]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h3052, hlam, p3183_0]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2013, hlam, p3183_1]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2633, hlam, p3183_1]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h3051, hlam, p3183_0]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [hlam, p3183_0]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h3054, hlam, p3183_0]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h2011, h3052, hc45, hlam, hphi, ht23, ht34, p3183_1, u2ehi3]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h1407, h2009, h2629, h3051, h3052, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p3067_1, p3183_1, u2ehi3]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [h3052, hc45, hlam, hphi, ht23, ht34, p3183_1, u2ehi3]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      rcases p3183_3 (m.d 0 5) (by simp) with h3209 | h3209
                                      · linarith only [h2014, h3209, hlam]
                                      · linarith only [h2013, h3209, hlam]
                                    · have p3183_0 := h3183c.1
                                      have p3183_1 := h3183c.2.1
                                      have p3183_2 := h3183c.2.2.1
                                      have p3183_3 := h3183c.2.2.2
                                      linarith only [hlam, p3183_0]
                                  · rcases h5bigk with h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c | h3213c
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [hlam, p3213_0]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h1407, hlam, p3213_1]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2013, h2629, h3052, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3067_1, p3213_1, u2ehi3]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2013, h2629, h3054, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3067_1, p3213_1]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2014, hlam, p3213_0]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2011, h2634, h3052, hc45, hlam, hphi, ht23, ht34, p3213_1, u2ehi3]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [hlam, p3213_0]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2634, h3052, hc45, hlam, hphi, ht23, ht34, p3213_1, u2ehi3]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      rcases p3213_3 (m.d 0 5) (by simp) with h3222 | h3222
                                      · linarith only [h1407, h3222, hlam]
                                      · linarith only [h2013, h3222, hlam]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2634, hlam, p3213_0]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2011, hlam, p3213_1]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2631, hlam, p3213_1]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [hlam, p3213_0]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h3051, h3054, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3056_1, p3213_1]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h3052, hlam, p3213_0]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2013, hlam, p3213_1]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2633, hlam, p3213_1]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h3051, hlam, p3213_0]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [hlam, p3213_0]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h3054, hlam, p3213_0]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h2011, h3052, hc45, hlam, hphi, ht23, ht34, p3213_1, u2ehi3]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h1407, h2009, h2629, h3051, h3052, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p3067_1, p3213_1, u2ehi3]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [h3052, hc45, hlam, hphi, ht23, ht34, p3213_1, u2ehi3]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      rcases p3213_3 (m.d 0 5) (by simp) with h3239 | h3239
                                      · linarith only [h2014, h3239, hlam]
                                      · linarith only [h2013, h3239, hlam]
                                    · have p3213_0 := h3213c.1
                                      have p3213_1 := h3213c.2.1
                                      have p3213_2 := h3213c.2.2.1
                                      have p3213_3 := h3213c.2.2.2
                                      linarith only [hlam, p3213_0]
                          · linarith only [h3172, h879, hlam]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        rcases p3067_3 (m.d 0 3) (by simp) with h3245 | h3245
                        · linarith only [h3245, h879, hlam]
                        · linarith only [h2009, h3245, hlam]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        rcases p3067_3 (m.d 0 3) (by simp) with h3248 | h3248
                        · linarith only [h3248, h879, hlam]
                        · linarith only [h2012, h3248, hlam]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        rcases p3067_3 (m.d 0 3) (by simp) with h3251 | h3251
                        · linarith only [h3251, h879, hlam]
                        · linarith only [h2013, h3251, hlam]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h2009, hlam, p3067_1]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h2629, hlam, p3067_1]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3056_1, p3067_1]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3056_1, p3067_1]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h2012, hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h2632, hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h3050, hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h3054, hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h2013, hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h2633, hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h3051, hlam, p3067_0]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [h0, h3051, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3056_1, p3067_1]
                      · have p3067_0 := h3067c.1
                        have p3067_1 := h3067c.2.1
                        have p3067_2 := h3067c.2.2.1
                        have p3067_3 := h3067c.2.2.2
                        linarith only [hlam, p3067_0]
              · linarith only [h2629, h3060, hlam]
            · linarith only [h3059, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            rcases p3056_3 (m.d 0 2) (by simp) with h3271 | h3271
            · rcases p3056_3 (m.d 1 2) (by simp) with h3272 | h3272
              · rcases p3056_3 (m.d 2 3) (by simp) with h3273 | h3273
                · linarith only [h2009, h3273, hlam]
                · linarith only [h3050, h3273, hlam]
              · linarith only [h2630, h3272, hlam]
            · linarith only [h3271, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            rcases p3056_3 (m.d 0 2) (by simp) with h3278 | h3278
            · rcases p3056_3 (m.d 1 2) (by simp) with h3279 | h3279
              · rcases p3056_3 (m.d 2 3) (by simp) with h3280 | h3280
                · linarith only [h2009, h3280, hlam]
                · linarith only [h3051, h3280, hlam]
              · linarith only [h2631, h3279, hlam]
            · linarith only [h3278, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h2009, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3056_1, u2ehi2]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            rcases p3056_3 (m.d 0 2) (by simp) with h3287 | h3287
            · linarith only [h0, h3287, hlam]
            · linarith only [h2009, h3287, hlam]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            rcases p3056_3 (m.d 0 2) (by simp) with h3290 | h3290
            · linarith only [h0, h3290, hlam]
            · linarith only [h2010, h3290, hlam]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            rcases p3056_3 (m.d 0 2) (by simp) with h3293 | h3293
            · linarith only [h0, h3293, hlam]
            · linarith only [h2011, h3293, hlam]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h2009, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h2629, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h2009, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3056_1, u2ehi3]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h0, h2009, h3052, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3056_1, u2ehi3]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h2010, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h2630, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h3050, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h3052, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h2011, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h2631, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [h3051, hlam, p3056_0]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [hc25, hlam, hphi, p3056_1, u2ehi3]
          · have p3056_0 := h3056c.1
            have p3056_1 := h3056c.2.1
            have p3056_2 := h3056c.2.2.1
            have p3056_3 := h3056c.2.2.2
            linarith only [hlam, p3056_0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h3311 | h3311
      · linarith only [h0, h2009, h2013, h2634, h3050, h3051, h3311, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3313 | h3313
        · linarith only [h2010, h2014, h3313, hc34, hlam, hphi, ht23, u2ehi3]
        · rcases h2bigk with h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c | h3315c
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h0, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            rcases p3315_3 (m.d 0 2) (by simp) with h3318 | h3318
            · rcases p3315_3 (m.d 1 2) (by simp) with h3319 | h3319
              · rcases p3315_3 (m.d 2 3) (by simp) with h3320 | h3320
                · linarith only [h3320, hlam, p3315_0]
                · rcases p3315_3 (m.d 2 4) (by simp) with h3322 | h3322
                  · linarith only [h2010, h3322, hlam]
                  · rcases p3315_3 (m.d 2 5) (by simp) with h3324 | h3324
                    · linarith only [h2011, h3324, hlam]
                    · linarith only [h3051, h3324, hlam]
              · linarith only [h2629, h3319, hlam]
            · linarith only [h3318, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            rcases p3315_3 (m.d 0 2) (by simp) with h3329 | h3329
            · rcases p3315_3 (m.d 1 2) (by simp) with h3330 | h3330
              · rcases p3315_3 (m.d 2 3) (by simp) with h3331 | h3331
                · linarith only [h2009, h3331, hlam]
                · linarith only [h3050, h3331, hlam]
              · linarith only [h2630, h3330, hlam]
            · linarith only [h3329, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            rcases p3315_3 (m.d 0 2) (by simp) with h3336 | h3336
            · rcases p3315_3 (m.d 1 2) (by simp) with h3337 | h3337
              · rcases p3315_3 (m.d 2 3) (by simp) with h3338 | h3338
                · linarith only [h2009, h3338, hlam]
                · rcases p3315_3 (m.d 2 4) (by simp) with h3340 | h3340
                  · linarith only [h2010, h3340, hlam]
                  · rcases p3315_3 (m.d 2 5) (by simp) with h3342 | h3342
                    · linarith only [h3342, hlam, p3315_0]
                    · rcases h3bigk with h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h879, hlam, p3344_1]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        rcases p3344_3 (m.d 0 3) (by simp) with h3347 | h3347
                        · rcases p3344_3 (m.d 1 3) (by simp) with h3348 | h3348
                          · rcases p3344_3 (m.d 2 3) (by simp) with h3349 | h3349
                            · linarith only [h2009, h3349, hlam]
                            · rcases p3344_3 (m.d 3 4) (by simp) with h3351 | h3351
                              · linarith only [h2012, h3351, hlam]
                              · rcases p3344_3 (m.d 3 5) (by simp) with h3353 | h3353
                                · linarith only [h2013, h3353, hlam]
                                · linarith only [h3051, h3353, hlam]
                          · linarith only [h2629, h3348, hlam]
                        · linarith only [h2009, h3347, hlam]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h2013, h3050, h3051, hlam, p3344_2]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h0, h2009, h3050, h3051, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3344_1, u2ehi3]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h2013, h2629, h3050, h3051, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3344_1, u2ehi3]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        rcases p3344_3 (m.d 0 3) (by simp) with h3362 | h3362
                        · linarith only [h3362, h879, hlam]
                        · linarith only [h2009, h3362, hlam]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h2013, h3050, h3051, h879, hlam, p3344_2]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h3050, h3051, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3344_1, u2ehi3]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h2009, hlam, p3344_1]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h2629, hlam, p3344_1]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h2013, h3051, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3344_1]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h3051, hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h2012, hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h2632, hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h3050, hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h3313, hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h2013, hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h2633, hlam, p3344_0]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [h1407, h2013, h2634, hc45, hlam, hphi, ht23, ht34, p3344_1, u2ehi2]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        rcases p3344_3 (m.d 0 3) (by simp) with h3380 | h3380
                        · rcases p3344_3 (m.d 1 3) (by simp) with h3381 | h3381
                          · rcases p3344_3 (m.d 2 3) (by simp) with h3382 | h3382
                            · linarith only [h3051, h3382, hlam]
                            · linarith only [h3050, h3382, hlam]
                          · linarith only [h2632, h3381, hlam]
                        · linarith only [h2012, h3380, hlam]
                      · have p3344_0 := h3344c.1
                        have p3344_1 := h3344c.2.1
                        have p3344_2 := h3344c.2.2.1
                        have p3344_3 := h3344c.2.2.2
                        linarith only [hlam, p3344_0]
              · linarith only [h2631, h3337, hlam]
            · linarith only [h3336, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h2009, h3050, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3315_1, u2ehi3]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            rcases p3315_3 (m.d 0 2) (by simp) with h3392 | h3392
            · linarith only [h0, h3392, hlam]
            · linarith only [h2009, h3392, hlam]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            rcases p3315_3 (m.d 0 2) (by simp) with h3395 | h3395
            · linarith only [h0, h3395, hlam]
            · linarith only [h2010, h3395, hlam]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            rcases p3315_3 (m.d 0 2) (by simp) with h3398 | h3398
            · linarith only [h0, h3398, hlam]
            · linarith only [h2011, h3398, hlam]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h2009, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h2629, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h2009, h2013, h3051, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3315_1, u2ehi3]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h3051, hlam, p3315_1]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h2010, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h2630, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h3050, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h3311, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h2011, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h2631, hlam, p3315_0]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [hc25, hlam, hphi, p3315_1, u2ehi2]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [h0, h2009, h2013, h3051, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3315_1, u2ehi3]
          · have p3315_0 := h3315c.1
            have p3315_1 := h3315c.2.1
            have p3315_2 := h3315c.2.2.1
            have p3315_3 := h3315c.2.2.2
            linarith only [hlam, p3315_0]
  · linarith only [h2012, h2014, h3050, hc45, hlam, hphi, ht23, ht34, u2ehi2]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2630 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2631 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h2632 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2633 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 1 4 5 (by decide) (by decide) with h2634 | h2634
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629 h2630 h2631 h2632 h2633 h2634
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629 h2630 h2631 h2632 h2633 h2634

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2630 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2631 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h2632 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2633 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  linarith only [h0, h2009, h2013, h2633, h879, hc01, hc12, hlam, hphi]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2630 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2631 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h2632 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 1 3 5 (by decide) (by decide) with h2633 | h2633
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629 h2630 h2631 h2632 h2633
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629 h2630 h2631 h2632 h2633

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2630 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2631 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h2632 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  linarith only [h2012, h2632, h879, hlam]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2630 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2631 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 1 3 4 (by decide) (by decide) with h2632 | h2632
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629 h2630 h2631 h2632
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629 h2630 h2631 h2632

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2630 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2631 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  linarith only [h0, h2009, h2631, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2630 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 1 2 5 (by decide) (by decide) with h2631 | h2631
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629 h2630 h2631
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629 h2630 h2631

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2630 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  linarith only [h0, h2009, h2630, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 1 2 4 (by decide) (by decide) with h2630 | h2630
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629 h2630
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629 h2630

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  linarith only [h0, h2010, h2629, hc23, hlam, hphi, u2ehi3]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 1 2 3 (by decide) (by decide) with h2629 | h2629
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014 h2629

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 0 4 5 (by decide) (by decide) with h2014 | h2014
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011 h2012 h2013 h2014

end R2N4
