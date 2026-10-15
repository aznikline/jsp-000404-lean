import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7926000 in
set_option maxHeartbeats 7926000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2669 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h2986 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h2987 | h2987
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2988 | h2988
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2989 | h2989
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2990 | h2990
        · linarith only [h0, h2990, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2992 | h2992
          · linarith only [h0, h2669, h2986, h2992, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2994 | h2994
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2995 | h2995
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2996 | h2996
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2997 | h2997
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2998 | h2998
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2999 | h2999
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3000 | h3000
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3001 | h3001
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
                              linarith only [h2994, h2999, h3001, hc02, hc45, hlam, hphi, ht0b, ht5b, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h4, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2669, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2999, h3001, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h0, hlam, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2990, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2992, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h0, h2999, h3001, hc01, hc45, hlam, hphi, ht0b, ht5b, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h0, h2669, h2994, h2999, h3001, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              rcases p3002_3 (m.d 0 2) (by simp) with h3017 | h3017
                              · linarith only [h3017, h4, hlam]
                              · linarith only [h2986, h3017, hlam]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h0, h2994, h2999, h3001, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2994, h2999, h3001, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2998, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              rcases p3002_3 (m.d 0 2) (by simp) with h3024 | h3024
                              · linarith only [h2669, h3024, hlam]
                              · linarith only [h2986, h3024, hlam]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2986, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2994, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2999, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h3000, hlam, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hlam, p3002_0]
                          · rcases h2bigk with h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c | h3032c
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2669, h2987, h2994, hc03, hc25, hlam, hphi, ht0b, ht5b, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h4, hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2669, hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2669, h2998, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h0, hlam, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2990, hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2992, hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2669, h2986, h2989, h3001, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h3000, h3001, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h0, h2994, h3000, h3001, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2994, h3000, h3001, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2998, hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2998, h3000, h3001, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2986, hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2994, hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h2999, hlam, p3032_0]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [h3000, hlam, p3032_1]
                            · have p3032_0 := h3032c.1
                              have p3032_1 := h3032c.2.1
                              have p3032_2 := h3032c.2.2.1
                              have p3032_3 := h3032c.2.2.2
                              linarith only [hlam, p3032_0]
                        · linarith only [h2669, h2989, h3000, hlam]
                      · linarith only [h2988, h2999, h4, hlam]
                    · linarith only [h0, h2987, h2994, h2998, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h2992, h2994, h2997, hlam]
                · linarith only [h2992, h2994, h2995, h2996, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3063 | h3063
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3064 | h3064
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3065 | h3065
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3066 | h3066
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3067 | h3067
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3068 | h3068
                          · rcases h2bigk with h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c | h3069c
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h2994, h3066, h3068, hc02, hc45, hlam, hphi, ht0b, ht5b, p3069_1]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h4, hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h2669, hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h3066, h3068, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3069_1]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h0, hlam, p3069_1]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h2990, hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h2992, hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h0, h3066, h3068, hc01, hc45, hlam, hphi, ht0b, ht5b, p3069_1]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p3069_1]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p3069_1]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h0, h2669, h2994, h3066, h3068, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3069_1]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              rcases p3069_3 (m.d 0 2) (by simp) with h3084 | h3084
                              · linarith only [h3084, h4, hlam]
                              · linarith only [h2986, h3084, hlam]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h0, h2994, h3066, h3068, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3069_1]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h2994, h3066, h3068, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3069_1]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h3065, hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              rcases p3069_3 (m.d 0 2) (by simp) with h3091 | h3091
                              · linarith only [h2669, h3091, hlam]
                              · linarith only [h2986, h3091, hlam]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h2986, hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h2994, hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h3066, hlam, p3069_0]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [h3067, hlam, p3069_1]
                            · have p3069_0 := h3069c.1
                              have p3069_1 := h3069c.2.1
                              have p3069_2 := h3069c.2.2.1
                              have p3069_3 := h3069c.2.2.2
                              linarith only [hlam, p3069_0]
                          · linarith only [h2989, h2990, h2994, h2995, h3066, h3068, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h2669, h2994, h3064, h3066, h3067, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h2988, h2994, h3066, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h2987, h2994, h3065, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h2990, h2994, h2995, h3064, hlam]
                · linarith only [h2990, h2994, h3063, hlam]
            · linarith only [h2986, h2994, h4, hc12, hc23, hlam, hphi]
      · linarith only [h2669, h2986, h2989, hlam]
    · linarith only [h2986, h2988, h4, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3108 | h3108
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3109 | h3109
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3110 | h3110
        · linarith only [h0, h2986, h3110, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3112 | h3112
          · linarith only [h0, h2669, h3112, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3114 | h3114
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3115 | h3115
              · linarith only [h0, h1, h2987, h3114, h3115, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3117 | h3117
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3118 | h3118
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3119 | h3119
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3120 | h3120
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3121 | h3121
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3122 | h3122
                          · rcases h2bigk with h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c | h3123c
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h3114, h3120, h3122, hc02, hc45, hlam, hphi, ht0b, ht5b, p3123_1]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h4, hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h2669, hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h2987, h3119, h3120, h3122, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3123_1]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h0, hlam, p3123_1]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h3110, hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h3112, hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h0, h3120, h3122, hc01, hc45, hlam, hphi, ht0b, ht5b, p3123_1]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p3123_1]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p3123_1]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h2987, h3119, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3123_1]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              rcases p3123_3 (m.d 0 2) (by simp) with h3138 | h3138
                              · linarith only [h3138, h4, hlam]
                              · linarith only [h2986, h3138, hlam]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h0, h3114, h3120, h3122, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3123_1]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h3114, h3120, h3122, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3123_1]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h3119, hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              rcases p3123_3 (m.d 0 2) (by simp) with h3145 | h3145
                              · linarith only [h2669, h3145, hlam]
                              · linarith only [h2986, h3145, hlam]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h2986, hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h3114, hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h3120, hlam, p3123_0]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [h3121, hlam, p3123_1]
                            · have p3123_0 := h3123c.1
                              have p3123_1 := h3123c.2.1
                              have p3123_2 := h3123c.2.2.1
                              have p3123_3 := h3123c.2.2.2
                              linarith only [hlam, p3123_0]
                          · linarith only [h2987, h3109, h3122, hlam]
                        · linarith only [h0, h2669, h3109, h3114, h3120, h3121, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1, h2987, h3110, h3114, h3119, h3120, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3156 | h3156
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3157 | h3157
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3158 | h3158
                          · rcases h2bigk with h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3114, h3156, h3158, hc02, hc45, hlam, hphi, ht0b, ht5b, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h4, hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h2669, hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3119, h3156, h3158, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h0, hlam, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3110, hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3112, hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h0, h3156, h3158, hc01, hc45, hlam, hphi, ht0b, ht5b, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3119, hc02, hc34, hlam, hphi, ht23, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3119, hc12, hc34, hlam, hphi, ht23, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3119, hlam, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3119, h3156, h3158, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h0, h3114, h3156, h3158, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3114, h3156, h3158, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3119, hc23, hc34, hlam, hphi, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              rcases p3159_3 (m.d 0 2) (by simp) with h3179 | h3179
                              · linarith only [h2669, h3179, hlam]
                              · linarith only [h2986, h3179, hlam]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h2986, hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3114, hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3156, hlam, p3159_0]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [h3157, hlam, p3159_1]
                            · have p3159_0 := h3159c.1
                              have p3159_1 := h3159c.2.1
                              have p3159_2 := h3159c.2.2.1
                              have p3159_3 := h3159c.2.2.2
                              linarith only [hlam, p3159_0]
                          · linarith only [h0, h2669, h3109, h3114, h3119, h3156, h3158, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h3114, h3118, h3119, h3156, h3157, h4, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h3108, h3114, h3156, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3110, h3114, h3115, h3118, hlam]
                · linarith only [h2987, h3108, h3110, h3114, h3117, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · linarith only [h2986, h2987, h3114, h4, hc12, hc34, hlam, hphi, ht23]
      · linarith only [h2986, h2987, h3109, h4, hlam]
    · linarith only [h2986, h3108, h4, hlam]

end R2N4
