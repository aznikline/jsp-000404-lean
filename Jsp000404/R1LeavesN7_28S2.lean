import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2965 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2966 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2967 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h2968 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2969 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2970 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 2 3 4 (by decide) (by decide) with h2971 | h2971
  · rcases m.htr 2 3 5 (by decide) (by decide) with h2972 | h2972
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2973 | h2973
      · linarith only [h1966, h1970, h2973, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h2975 | h2975
        · linarith only [h1965, h1966, h1970, h2971, h2975, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
        · rcases h0bigk with h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [hlam, p2977_0]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h0, hlam, p2977_1]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1414, hlam, p2977_0]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h0, h1966, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2977_1, u2ehi3]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1728, hlam, p2977_1]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            rcases p2977_3 (m.d 0 1) (by simp) with h2983 | h2983
            · linarith only [h0, h2983, hlam]
            · rcases p2977_3 (m.d 0 2) (by simp) with h2985 | h2985
              · rcases p2977_3 (m.d 0 3) (by simp) with h2986 | h2986
                · linarith only [h1965, h2986, hlam]
                · linarith only [h1414, h2986, hlam]
              · linarith only [h0, h2985, hlam]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [hlam, p2977_0]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            rcases p2977_3 (m.d 0 1) (by simp) with h2991 | h2991
            · linarith only [h0, h2991, hlam]
            · rcases p2977_3 (m.d 0 2) (by simp) with h2993 | h2993
              · rcases p2977_3 (m.d 0 3) (by simp) with h2994 | h2994
                · linarith only [h1965, h2994, hlam]
                · rcases p2977_3 (m.d 0 4) (by simp) with h2996 | h2996
                  · linarith only [h1966, h2996, hlam]
                  · rcases p2977_3 (m.d 0 5) (by simp) with h2998 | h2998
                    · linarith only [h1967, h2998, hlam]
                    · rcases h0emax with h3000 | h3000 | h3000 | h3000 | h3000
                      · rcases h5bigk with h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [hlam, p3001_0]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h1728, hlam, p3001_1]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h0, h1969, h2973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2977_1, p3001_1, u2ehi3]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h0, h1969, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2977_1, p3001_1]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h1970, hlam, p3001_1]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h1728, hc01, hc15, hlam, hphi, p3001_1]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [hlam, p3001_0]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h2967, h2973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3001_1, u2ehi3]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          rcases p3001_3 (m.d 0 5) (by simp) with h3010 | h3010
                          · linarith only [h1728, h3010, hlam]
                          · linarith only [h1969, h3010, hlam]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h1966, h1970, h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3001_1, u2ehi3]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h1967, hlam, p3001_1]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h2967, hlam, p3001_1]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [hlam, p3001_0]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h0, h1967, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3001_1]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h2973, hlam, p3001_1]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h1969, hlam, p3001_0]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h2969, hlam, p3001_0]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h2972, hlam, p3001_0]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [hlam, p3001_0]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h2975, hlam, p3001_1]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3001_1, u2ehi4]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h2970, hlam, p3001_0]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3001_1, u2ehi4]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [h2965, h2968, h2970, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3001_1]
                        · have p3001_0 := h3001c.1
                          have p3001_1 := h3001c.2.1
                          have p3001_2 := h3001c.2.2.1
                          have p3001_3 := h3001c.2.2.2
                          linarith only [hlam, p3001_0]
                      · linarith only [h3000, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2977_1]
                      · rcases h5bigk with h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c | h3030c
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [hlam, p3030_0]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h1728, hlam, p3030_1]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h1969, h2973, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2977_1, p3030_1, u2ehi3]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h0, h1969, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2977_1, p3030_1]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h1970, hlam, p3030_1]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h1728, h2965, h2968, h2970, hc01, hc12, hlam, hphi, p3030_1]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [hlam, p3030_0]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h2965, h2968, h2970, h2973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3030_1, u2ehi3]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          rcases p3030_3 (m.d 0 5) (by simp) with h3039 | h3039
                          · linarith only [h1728, h3039, hlam]
                          · linarith only [h1969, h3039, hlam]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h1966, h1970, h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3030_1, u2ehi3]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h1967, hlam, p3030_1]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h2967, hlam, p3030_1]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [hlam, p3030_0]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h0, h1965, h2972, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3030_1]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h2973, hlam, p3030_1]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h1969, hlam, p3030_0]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h2969, hlam, p3030_0]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h2972, hlam, p3030_0]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [hlam, p3030_0]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h2975, hlam, p3030_1]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3030_1, u2ehi4]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h2970, hlam, p3030_0]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3030_1, u2ehi4]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [h2965, h2968, h2970, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3030_1]
                        · have p3030_0 := h3030c.1
                          have p3030_1 := h3030c.2.1
                          have p3030_2 := h3030c.2.2.1
                          have p3030_3 := h3030c.2.2.2
                          linarith only [hlam, p3030_0]
                      · rcases h5bigk with h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [hlam, p3058_0]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h1728, hlam, p3058_1]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h2973, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3058_1, u2ehi3]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h0, h1969, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2977_1, p3058_1]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h1970, hlam, p3058_1]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h1728, h2965, h2968, h2970, hc01, hc12, hlam, hphi, p3058_1]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [hlam, p3058_0]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h2965, h2968, h2970, h2973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3058_1, u2ehi3]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          rcases p3058_3 (m.d 0 5) (by simp) with h3067 | h3067
                          · linarith only [h1728, h3067, hlam]
                          · linarith only [h1969, h3067, hlam]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h1966, h1970, h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3058_1, u2ehi3]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h1967, hlam, p3058_1]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h2967, hlam, p3058_1]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [hlam, p3058_0]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h0, h1967, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3058_1]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h2973, hlam, p3058_1]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h1969, hlam, p3058_0]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h2969, hlam, p3058_0]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h2972, hlam, p3058_0]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [hlam, p3058_0]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h2975, hlam, p3058_1]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3058_1, u2ehi4]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h2970, hlam, p3058_0]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3058_1, u2ehi4]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [h2965, h2968, h2970, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3058_1]
                        · have p3058_0 := h3058c.1
                          have p3058_1 := h3058c.2.1
                          have p3058_2 := h3058c.2.2.1
                          have p3058_3 := h3058c.2.2.2
                          linarith only [hlam, p3058_0]
                      · rcases h5bigk with h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c | h3086c
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [hlam, p3086_0]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h1728, hlam, p3086_1]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h2973, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3086_1, u2ehi3]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h0, h1969, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2977_1, p3086_1]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h1970, hlam, p3086_1]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h1728, h2965, h2968, h2970, hc01, hc12, hlam, hphi, p3086_1]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [hlam, p3086_0]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h2965, h2968, h2970, h2973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3086_1, u2ehi3]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          rcases p3086_3 (m.d 0 5) (by simp) with h3095 | h3095
                          · linarith only [h1728, h3095, hlam]
                          · linarith only [h1969, h3095, hlam]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h1966, h1970, h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3086_1, u2ehi3]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h1967, hlam, p3086_1]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h2967, hlam, p3086_1]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [hlam, p3086_0]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h0, h1967, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3086_1]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h2973, hlam, p3086_1]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h1969, hlam, p3086_0]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h2969, hlam, p3086_0]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h2972, hlam, p3086_0]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [hlam, p3086_0]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h2975, hlam, p3086_1]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3086_1, u2ehi4]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h2970, hlam, p3086_0]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3086_1, u2ehi4]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [h2965, h2968, h2970, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3086_1]
                        · have p3086_0 := h3086c.1
                          have p3086_1 := h3086c.2.1
                          have p3086_2 := h3086c.2.2.1
                          have p3086_3 := h3086c.2.2.2
                          linarith only [hlam, p3086_0]
              · linarith only [h1965, h2993, hlam]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            rcases p2977_3 (m.d 0 1) (by simp) with h3115 | h3115
            · linarith only [h0, h3115, hlam]
            · rcases p2977_3 (m.d 0 2) (by simp) with h3117 | h3117
              · rcases p2977_3 (m.d 0 3) (by simp) with h3118 | h3118
                · linarith only [h1965, h3118, hlam]
                · linarith only [h1968, h3118, hlam]
              · linarith only [h1966, h3117, hlam]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            rcases p2977_3 (m.d 0 1) (by simp) with h3122 | h3122
            · linarith only [h0, h3122, hlam]
            · rcases p2977_3 (m.d 0 2) (by simp) with h3124 | h3124
              · rcases p2977_3 (m.d 0 3) (by simp) with h3125 | h3125
                · linarith only [h1965, h3125, hlam]
                · linarith only [h1969, h3125, hlam]
              · linarith only [h1967, h3124, hlam]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            rcases p2977_3 (m.d 0 1) (by simp) with h3129 | h3129
            · linarith only [h1414, h3129, hlam]
            · rcases p2977_3 (m.d 0 2) (by simp) with h3131 | h3131
              · rcases p2977_3 (m.d 0 3) (by simp) with h3132 | h3132
                · rcases p2977_3 (m.d 0 4) (by simp) with h3133 | h3133
                  · linarith only [h1968, h3133, hlam]
                  · rcases p2977_3 (m.d 0 5) (by simp) with h3135 | h3135
                    · linarith only [h1969, h3135, hlam]
                    · linarith only [h1728, h3135, hlam]
                · linarith only [h1414, h3132, hlam]
              · linarith only [h0, h3131, hlam]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1965, hlam, p2977_1]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [hlam, p2977_0]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            rcases p2977_3 (m.d 0 1) (by simp) with h3142 | h3142
            · linarith only [h1414, h3142, hlam]
            · rcases p2977_3 (m.d 0 2) (by simp) with h3144 | h3144
              · rcases p2977_3 (m.d 0 3) (by simp) with h3145 | h3145
                · rcases p2977_3 (m.d 0 4) (by simp) with h3146 | h3146
                  · linarith only [h1968, h3146, hlam]
                  · rcases p2977_3 (m.d 0 5) (by simp) with h3148 | h3148
                    · linarith only [h1969, h3148, hlam]
                    · linarith only [h1970, h3148, hlam]
                · linarith only [h1968, h3145, hlam]
              · linarith only [h1966, h3144, hlam]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            rcases p2977_3 (m.d 0 1) (by simp) with h3153 | h3153
            · linarith only [h1414, h3153, hlam]
            · rcases p2977_3 (m.d 0 2) (by simp) with h3155 | h3155
              · rcases p2977_3 (m.d 0 3) (by simp) with h3156 | h3156
                · rcases p2977_3 (m.d 0 4) (by simp) with h3157 | h3157
                  · linarith only [h1968, h3157, hlam]
                  · rcases p2977_3 (m.d 0 5) (by simp) with h3159 | h3159
                    · linarith only [h1969, h3159, hlam]
                    · rcases h0emax with h3161 | h3161 | h3161 | h3161 | h3161
                      · rcases h5bigk with h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c | h3162c
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [hlam, p3162_0]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h1728, hlam, p3162_1]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h2973, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2977_1, p3162_1, u2ehi3]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h1414, h2965, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2977_1, p3162_1]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h1970, hlam, p3162_1]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h1728, h2965, h2968, h2970, hc01, hc12, hlam, hphi, p3162_1]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [hlam, p3162_0]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h2965, h2968, h2970, h2973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3162_1, u2ehi3]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          rcases p3162_3 (m.d 0 5) (by simp) with h3171 | h3171
                          · linarith only [h1728, h3171, hlam]
                          · linarith only [h1969, h3171, hlam]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h1966, h1970, h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3162_1, u2ehi3]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h1967, hlam, p3162_1]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h2967, hlam, p3162_1]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [hlam, p3162_0]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h0, h1967, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3162_1]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h2973, hlam, p3162_1]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h1969, hlam, p3162_0]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h2969, hlam, p3162_0]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h2972, hlam, p3162_0]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [hlam, p3162_0]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h2975, hlam, p3162_1]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3162_1, u2ehi4]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h2970, hlam, p3162_0]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3162_1, u2ehi4]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [h2965, h2968, h2970, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3162_1]
                        · have p3162_0 := h3162c.1
                          have p3162_1 := h3162c.2.1
                          have p3162_2 := h3162c.2.2.1
                          have p3162_3 := h3162c.2.2.2
                          linarith only [hlam, p3162_0]
                      · linarith only [h1965, h3161, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1966, h1970, h3161, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2977_1, u2ehi3]
                      · rcases h5bigk with h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [hlam, p3192_0]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h1728, hlam, p3192_1]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h1965, h2973, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2977_1, p3192_1, u2ehi3]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h0, h1965, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2977_1, p3192_1]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h1970, hlam, p3192_1]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h1728, h2965, h2968, h2970, hc01, hc12, hlam, hphi, p3192_1]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [hlam, p3192_0]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h2965, h2968, h2970, h2973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3192_1, u2ehi3]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          rcases p3192_3 (m.d 0 5) (by simp) with h3201 | h3201
                          · linarith only [h1728, h3201, hlam]
                          · linarith only [h1969, h3201, hlam]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h1966, h1970, h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3192_1, u2ehi3]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h1967, hlam, p3192_1]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h2967, hlam, p3192_1]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [hlam, p3192_0]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h0, h1965, h2972, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3192_1]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h2973, hlam, p3192_1]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h1969, hlam, p3192_0]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h2969, hlam, p3192_0]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h2972, hlam, p3192_0]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [hlam, p3192_0]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h2975, hlam, p3192_1]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3192_1, u2ehi4]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h2970, hlam, p3192_0]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3192_1, u2ehi4]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [h2965, h2968, h2970, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3192_1]
                        · have p3192_0 := h3192c.1
                          have p3192_1 := h3192c.2.1
                          have p3192_2 := h3192c.2.2.1
                          have p3192_3 := h3192c.2.2.2
                          linarith only [hlam, p3192_0]
                      · rcases h5bigk with h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c | h3220c
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [hlam, p3220_0]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h1728, hlam, p3220_1]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h2973, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3220_1, u2ehi3]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h0, h1965, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2977_1, p3220_1]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h1970, hlam, p3220_1]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h1728, h2965, h2968, h2970, hc01, hc12, hlam, hphi, p3220_1]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [hlam, p3220_0]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h2965, h2968, h2970, h2973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3220_1, u2ehi3]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          rcases p3220_3 (m.d 0 5) (by simp) with h3229 | h3229
                          · linarith only [h1728, h3229, hlam]
                          · linarith only [h1969, h3229, hlam]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h1966, h1970, h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3220_1, u2ehi3]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h1967, hlam, p3220_1]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h2967, hlam, p3220_1]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [hlam, p3220_0]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h0, h1967, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3220_1]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h2973, hlam, p3220_1]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h1969, hlam, p3220_0]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h2969, hlam, p3220_0]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h2972, hlam, p3220_0]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [hlam, p3220_0]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h2975, hlam, p3220_1]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3220_1, u2ehi4]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h2970, hlam, p3220_0]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3220_1, u2ehi4]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [h2965, h2968, h2970, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3220_1]
                        · have p3220_0 := h3220c.1
                          have p3220_1 := h3220c.2.1
                          have p3220_2 := h3220c.2.2.1
                          have p3220_3 := h3220c.2.2.2
                          linarith only [hlam, p3220_0]
                · linarith only [h1969, h3156, hlam]
              · linarith only [h1967, h3155, hlam]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1970, h2965, h2968, h2970, hc01, hc12, hlam, hphi, p2977_1]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1966, hlam, p2977_0]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1968, hlam, p2977_0]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [hlam, p2977_0]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1970, hlam, p2977_0]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1970, h2965, h2968, h2970, hc01, hc12, hlam, hphi, p2977_1]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1967, hlam, p2977_1]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1969, hlam, p2977_0]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [h1966, h1970, h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2977_1, u2ehi3]
          · have p2977_0 := h2977c.1
            have p2977_1 := h2977c.2.1
            have p2977_2 := h2977c.2.2.1
            have p2977_3 := h2977c.2.2.2
            linarith only [hlam, p2977_0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h3260 | h3260
      · linarith only [h1969, h1970, h2972, h3260, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3262 | h3262
        · linarith only [h1969, h1970, h2971, h2972, h3262, hc34, hlam, hphi, ht23, u2ehi3]
        · rcases h0bigk with h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c | h3264c
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [hlam, p3264_0]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h0, hlam, p3264_1]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1414, hlam, p3264_0]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h0, h1966, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3264_1, u2ehi3]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1728, hlam, p3264_1]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            rcases p3264_3 (m.d 0 1) (by simp) with h3270 | h3270
            · linarith only [h0, h3270, hlam]
            · rcases p3264_3 (m.d 0 2) (by simp) with h3272 | h3272
              · rcases p3264_3 (m.d 0 3) (by simp) with h3273 | h3273
                · linarith only [h1965, h3273, hlam]
                · linarith only [h1414, h3273, hlam]
              · linarith only [h0, h3272, hlam]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [hlam, p3264_0]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h0, h1969, h2972, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3264_1]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            rcases p3264_3 (m.d 0 1) (by simp) with h3279 | h3279
            · linarith only [h0, h3279, hlam]
            · rcases p3264_3 (m.d 0 2) (by simp) with h3281 | h3281
              · rcases p3264_3 (m.d 0 3) (by simp) with h3282 | h3282
                · linarith only [h1965, h3282, hlam]
                · linarith only [h1968, h3282, hlam]
              · linarith only [h1966, h3281, hlam]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h0, h1969, h2971, h2972, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3264_1, u2ehi3]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            rcases p3264_3 (m.d 0 1) (by simp) with h3287 | h3287
            · linarith only [h1414, h3287, hlam]
            · rcases p3264_3 (m.d 0 2) (by simp) with h3289 | h3289
              · rcases p3264_3 (m.d 0 3) (by simp) with h3290 | h3290
                · rcases p3264_3 (m.d 0 4) (by simp) with h3291 | h3291
                  · linarith only [h1968, h3291, hlam]
                  · rcases p3264_3 (m.d 0 5) (by simp) with h3293 | h3293
                    · linarith only [h1969, h3293, hlam]
                    · linarith only [h1728, h3293, hlam]
                · linarith only [h1414, h3290, hlam]
              · linarith only [h0, h3289, hlam]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1965, hlam, p3264_1]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [hlam, p3264_0]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            rcases p3264_3 (m.d 0 1) (by simp) with h3300 | h3300
            · linarith only [h1414, h3300, hlam]
            · rcases p3264_3 (m.d 0 2) (by simp) with h3302 | h3302
              · rcases p3264_3 (m.d 0 3) (by simp) with h3303 | h3303
                · rcases p3264_3 (m.d 0 4) (by simp) with h3304 | h3304
                  · linarith only [h1968, h3304, hlam]
                  · rcases p3264_3 (m.d 0 5) (by simp) with h3306 | h3306
                    · linarith only [h1969, h3306, hlam]
                    · linarith only [h1970, h3306, hlam]
                · linarith only [h1968, h3303, hlam]
              · linarith only [h1966, h3302, hlam]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1969, h2971, h2972, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3264_1, u2ehi3]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1970, h2965, h2968, h2970, hc01, hc12, hlam, hphi, p3264_1]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1966, hlam, p3264_0]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1968, hlam, p3264_0]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [hlam, p3264_0]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1970, hlam, p3264_0]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1970, h2965, h2968, h2970, hc01, hc12, hlam, hphi, p3264_1]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1967, hlam, p3264_1]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1969, hlam, p3264_0]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [h1966, h1970, h2965, h2968, h2970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3264_1, u2ehi3]
          · have p3264_0 := h3264c.1
            have p3264_1 := h3264c.2.1
            have p3264_2 := h3264c.2.2.1
            have p3264_3 := h3264c.2.2.2
            linarith only [hlam, p3264_0]
  · linarith only [h1968, h1970, h2965, h2968, h2970, h2971, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]

end R2N4
