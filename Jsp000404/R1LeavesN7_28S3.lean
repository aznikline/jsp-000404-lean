import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S1
import Jsp000404.R1LeavesN7_28S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h2970 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h3323 | h3323
  · rcases m.htr 2 3 5 (by decide) (by decide) with h3324 | h3324
    · rcases m.htr 2 4 5 (by decide) (by decide) with h3325 | h3325
      · linarith only [h0, h1728, h1965, h2970, h3323, h3325, hc01, hc12, hlam, hphi]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3327 | h3327
        · linarith only [h0, h1965, h1966, h1970, h3323, h3327, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
        · rcases h0bigk with h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [hlam, p3329_0]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h0, hlam, p3329_1]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1414, hlam, p3329_0]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1728, h1966, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3329_1, u2ehi3]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1728, hlam, p3329_1]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            rcases p3329_3 (m.d 0 1) (by simp) with h3335 | h3335
            · linarith only [h0, h3335, hlam]
            · rcases p3329_3 (m.d 0 2) (by simp) with h3337 | h3337
              · rcases p3329_3 (m.d 0 3) (by simp) with h3338 | h3338
                · linarith only [h1965, h3338, hlam]
                · linarith only [h1414, h3338, hlam]
              · linarith only [h0, h3337, hlam]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [hlam, p3329_0]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            rcases p3329_3 (m.d 0 1) (by simp) with h3343 | h3343
            · linarith only [h0, h3343, hlam]
            · rcases p3329_3 (m.d 0 2) (by simp) with h3345 | h3345
              · rcases p3329_3 (m.d 0 3) (by simp) with h3346 | h3346
                · linarith only [h1965, h3346, hlam]
                · rcases p3329_3 (m.d 0 4) (by simp) with h3348 | h3348
                  · linarith only [h1966, h3348, hlam]
                  · rcases p3329_3 (m.d 0 5) (by simp) with h3350 | h3350
                    · linarith only [h1967, h3350, hlam]
                    · rcases h0emax with h3352 | h3352 | h3352 | h3352 | h3352
                      · rcases h5bigk with h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [hlam, p3353_0]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h1728, hlam, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h3325, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3353_1, u2ehi3]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h0, h1969, h3327, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3329_1, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h1970, hlam, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h1728, h2970, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [hlam, p3353_0]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h2970, h3325, hc45, hlam, hphi, ht23, ht34, p3353_1, u2ehi3]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h2970, h3327, hc34, hc45, hlam, hphi, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h2970, hlam, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h1967, hlam, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h2967, hlam, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [hlam, p3353_0]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h0, h1967, h1969, h3327, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3329_1, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h3325, hlam, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h1969, hlam, p3353_0]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h2969, hlam, p3353_0]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h3324, hlam, p3353_0]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [hlam, p3353_0]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h3327, hlam, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h1967, h3325, hc45, hlam, hphi, ht23, ht34, p3353_1, u2ehi3]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h0, h1728, h1967, h1969, h3325, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p3329_1, p3353_1, u2ehi3]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h3325, hc45, hlam, hphi, ht23, ht34, p3353_1, u2ehi3]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [h3327, hc34, hc45, hlam, hphi, p3353_1]
                        · have p3353_0 := h3353c.1
                          have p3353_1 := h3353c.2.1
                          have p3353_2 := h3353c.2.2.1
                          have p3353_3 := h3353c.2.2.2
                          linarith only [hlam, p3353_0]
                      · linarith only [h1967, h1969, h3325, h3352, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3329_1, u2ehi3]
                      · rcases h5bigk with h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [hlam, p3380_0]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h1728, hlam, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h0, h1969, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3329_1, p3380_1, u2ehi3]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h0, h1969, h3327, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3329_1, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h1970, hlam, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h1728, hc01, hc15, hlam, hphi, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [hlam, p3380_0]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h2967, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3380_1, u2ehi3]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h2970, h3327, hc34, hc45, hlam, hphi, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h2970, hlam, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h1967, hlam, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h2967, hlam, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [hlam, p3380_0]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h1728, h1967, h2970, h3327, hc34, hc45, hlam, hphi, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h3325, hlam, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h1969, hlam, p3380_0]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h2969, hlam, p3380_0]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h3324, hlam, p3380_0]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [hlam, p3380_0]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h3327, hlam, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h1728, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h0, h1728, h1965, h3324, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p3329_1, p3380_1, u2ehi4]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [hc45, hlam, hphi, ht23, ht34, p3380_1, u2ehi4]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [h3327, hc34, hc45, hlam, hphi, p3380_1]
                        · have p3380_0 := h3380c.1
                          have p3380_1 := h3380c.2.1
                          have p3380_2 := h3380c.2.2.1
                          have p3380_3 := h3380c.2.2.2
                          linarith only [hlam, p3380_0]
                      · rcases h5bigk with h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [hlam, p3406_0]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h1728, hlam, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h0, h1969, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3329_1, p3406_1, u2ehi3]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h0, h1969, h3327, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3329_1, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h1970, hlam, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h1728, hc01, hc15, hlam, hphi, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [hlam, p3406_0]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h2967, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3406_1, u2ehi3]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h2970, h3327, hc34, hc45, hlam, hphi, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h2970, hlam, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h1967, hlam, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h2967, hlam, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [hlam, p3406_0]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h0, h1965, h3324, h3327, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h3325, hlam, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h1969, hlam, p3406_0]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h2969, hlam, p3406_0]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h3324, hlam, p3406_0]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [hlam, p3406_0]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h3327, hlam, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3406_1, u2ehi4]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h1728, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [hc45, hlam, hphi, ht23, ht34, p3406_1, u2ehi4]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [h3327, hc34, hc45, hlam, hphi, p3406_1]
                        · have p3406_0 := h3406c.1
                          have p3406_1 := h3406c.2.1
                          have p3406_2 := h3406c.2.2.1
                          have p3406_3 := h3406c.2.2.2
                          linarith only [hlam, p3406_0]
                      · rcases h5bigk with h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c | h3432c
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [hlam, p3432_0]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h1728, hlam, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h0, h1969, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3329_1, p3432_1, u2ehi3]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h0, h1969, h3327, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3329_1, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h1970, hlam, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h1728, hc01, hc15, hlam, hphi, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [hlam, p3432_0]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h2967, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3432_1, u2ehi3]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h2970, h3327, hc34, hc45, hlam, hphi, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h2970, hlam, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h1967, hlam, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h2967, hlam, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [hlam, p3432_0]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h1728, h1967, h2970, h3327, hc34, hc45, hlam, hphi, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h3325, hlam, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h1969, hlam, p3432_0]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h2969, hlam, p3432_0]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h3324, hlam, p3432_0]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [hlam, p3432_0]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h3327, hlam, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h1728, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h0, h1728, h1965, h3324, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p3329_1, p3432_1, u2ehi4]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [hc45, hlam, hphi, ht23, ht34, p3432_1, u2ehi4]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [h3327, hc34, hc45, hlam, hphi, p3432_1]
                        · have p3432_0 := h3432c.1
                          have p3432_1 := h3432c.2.1
                          have p3432_2 := h3432c.2.2.1
                          have p3432_3 := h3432c.2.2.2
                          linarith only [hlam, p3432_0]
              · linarith only [h1965, h3345, hlam]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            rcases p3329_3 (m.d 0 1) (by simp) with h3459 | h3459
            · linarith only [h0, h3459, hlam]
            · rcases p3329_3 (m.d 0 2) (by simp) with h3461 | h3461
              · rcases p3329_3 (m.d 0 3) (by simp) with h3462 | h3462
                · linarith only [h1965, h3462, hlam]
                · linarith only [h1968, h3462, hlam]
              · linarith only [h1966, h3461, hlam]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            rcases p3329_3 (m.d 0 1) (by simp) with h3466 | h3466
            · linarith only [h0, h3466, hlam]
            · rcases p3329_3 (m.d 0 2) (by simp) with h3468 | h3468
              · rcases p3329_3 (m.d 0 3) (by simp) with h3469 | h3469
                · linarith only [h1965, h3469, hlam]
                · linarith only [h1969, h3469, hlam]
              · linarith only [h1967, h3468, hlam]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            rcases p3329_3 (m.d 0 1) (by simp) with h3473 | h3473
            · linarith only [h1414, h3473, hlam]
            · rcases p3329_3 (m.d 0 2) (by simp) with h3475 | h3475
              · rcases p3329_3 (m.d 0 3) (by simp) with h3476 | h3476
                · rcases p3329_3 (m.d 0 4) (by simp) with h3477 | h3477
                  · linarith only [h1968, h3477, hlam]
                  · rcases p3329_3 (m.d 0 5) (by simp) with h3479 | h3479
                    · linarith only [h1969, h3479, hlam]
                    · linarith only [h1728, h3479, hlam]
                · linarith only [h1414, h3476, hlam]
              · linarith only [h0, h3475, hlam]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1965, hlam, p3329_1]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [hlam, p3329_0]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            rcases p3329_3 (m.d 0 1) (by simp) with h3486 | h3486
            · linarith only [h1414, h3486, hlam]
            · rcases p3329_3 (m.d 0 2) (by simp) with h3488 | h3488
              · rcases p3329_3 (m.d 0 3) (by simp) with h3489 | h3489
                · rcases p3329_3 (m.d 0 4) (by simp) with h3490 | h3490
                  · linarith only [h1968, h3490, hlam]
                  · rcases p3329_3 (m.d 0 5) (by simp) with h3492 | h3492
                    · linarith only [h1969, h3492, hlam]
                    · linarith only [h1970, h3492, hlam]
                · linarith only [h1968, h3489, hlam]
              · linarith only [h1966, h3488, hlam]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            rcases p3329_3 (m.d 0 1) (by simp) with h3497 | h3497
            · linarith only [h1414, h3497, hlam]
            · rcases p3329_3 (m.d 0 2) (by simp) with h3499 | h3499
              · rcases p3329_3 (m.d 0 3) (by simp) with h3500 | h3500
                · rcases p3329_3 (m.d 0 4) (by simp) with h3501 | h3501
                  · linarith only [h1968, h3501, hlam]
                  · rcases p3329_3 (m.d 0 5) (by simp) with h3503 | h3503
                    · linarith only [h1969, h3503, hlam]
                    · rcases h0emax with h3505 | h3505 | h3505 | h3505 | h3505
                      · rcases h5bigk with h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c | h3506c
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [hlam, p3506_0]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h1728, hlam, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h1414, h2965, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3329_1, p3506_1, u2ehi3]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h1414, h2965, h3327, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3329_1, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h1970, hlam, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h1728, hc01, hc15, hlam, hphi, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [hlam, p3506_0]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h2967, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3506_1, u2ehi3]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h2970, h3327, hc34, hc45, hlam, hphi, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h2970, hlam, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h1967, hlam, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h2967, hlam, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [hlam, p3506_0]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h1728, h1967, h2970, h3327, hc34, hc45, hlam, hphi, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h3325, hlam, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h1969, hlam, p3506_0]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h2969, hlam, p3506_0]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h3324, hlam, p3506_0]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [hlam, p3506_0]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h3327, hlam, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3506_1, u2ehi4]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h1728, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [hc45, hlam, hphi, ht23, ht34, p3506_1, u2ehi4]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [h3327, hc34, hc45, hlam, hphi, p3506_1]
                        · have p3506_0 := h3506c.1
                          have p3506_1 := h3506c.2.1
                          have p3506_2 := h3506c.2.2.1
                          have p3506_3 := h3506c.2.2.2
                          linarith only [hlam, p3506_0]
                      · linarith only [h1965, h3505, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1966, h1970, h3505, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3329_1, u2ehi3]
                      · rcases h5bigk with h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c | h3534c
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [hlam, p3534_0]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h1728, hlam, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h1414, h2965, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3329_1, p3534_1, u2ehi3]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h1414, h2965, h3327, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3329_1, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h1970, hlam, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h1728, hc01, hc15, hlam, hphi, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [hlam, p3534_0]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h2967, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3534_1, u2ehi3]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h2970, h3327, hc34, hc45, hlam, hphi, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h2970, hlam, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h1967, hlam, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h2967, hlam, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [hlam, p3534_0]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h1728, h1967, h2970, h3327, hc34, hc45, hlam, hphi, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h3325, hlam, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h1969, hlam, p3534_0]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h2969, hlam, p3534_0]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h3324, hlam, p3534_0]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [hlam, p3534_0]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h3327, hlam, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3534_1, u2ehi4]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h1728, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [hc45, hlam, hphi, ht23, ht34, p3534_1, u2ehi4]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [h3327, hc34, hc45, hlam, hphi, p3534_1]
                        · have p3534_0 := h3534c.1
                          have p3534_1 := h3534c.2.1
                          have p3534_2 := h3534c.2.2.1
                          have p3534_3 := h3534c.2.2.2
                          linarith only [hlam, p3534_0]
                      · rcases h5bigk with h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c | h3560c
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [hlam, p3560_0]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h1728, hlam, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h1414, h2965, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3329_1, p3560_1, u2ehi3]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h1414, h2965, h3327, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3329_1, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h1970, hlam, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h1728, hc01, hc15, hlam, hphi, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [hlam, p3560_0]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h2967, h3325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3560_1, u2ehi3]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h2970, h3327, hc34, hc45, hlam, hphi, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h2970, hlam, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h1967, hlam, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h2967, hlam, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [hlam, p3560_0]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h1728, h1967, h2970, h3327, hc34, hc45, hlam, hphi, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h3325, hlam, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h1969, hlam, p3560_0]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h2969, hlam, p3560_0]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h3324, hlam, p3560_0]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [hlam, p3560_0]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h3327, hlam, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h1967, hc45, hlam, hphi, ht23, ht34, p3560_1, u2ehi4]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h1728, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [hc45, hlam, hphi, ht23, ht34, p3560_1, u2ehi4]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [h3327, hc34, hc45, hlam, hphi, p3560_1]
                        · have p3560_0 := h3560c.1
                          have p3560_1 := h3560c.2.1
                          have p3560_2 := h3560c.2.2.1
                          have p3560_3 := h3560c.2.2.2
                          linarith only [hlam, p3560_0]
                · linarith only [h1969, h3500, hlam]
              · linarith only [h1967, h3499, hlam]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1970, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3329_1]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1966, hlam, p3329_0]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1968, hlam, p3329_0]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [hlam, p3329_0]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1970, hlam, p3329_0]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            rcases p3329_3 (m.d 0 1) (by simp) with h3593 | h3593
            · linarith only [h1728, h3593, hlam]
            · rcases p3329_3 (m.d 0 2) (by simp) with h3595 | h3595
              · rcases p3329_3 (m.d 0 3) (by simp) with h3596 | h3596
                · rcases p3329_3 (m.d 0 4) (by simp) with h3597 | h3597
                  · linarith only [h1970, h3597, hlam]
                  · linarith only [h1966, h1970, h3597, hc45, hlam, hphi, ht23, ht34, p3329_1, u2ehi3]
                · linarith only [h1414, h3596, hlam]
              · linarith only [h0, h3595, hlam]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1967, hlam, p3329_1]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1969, hlam, p3329_0]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [h1966, h1970, hc45, hlam, hphi, ht23, ht34, p3329_1, u2ehi3]
          · have p3329_0 := h3329c.1
            have p3329_1 := h3329c.2.1
            have p3329_2 := h3329c.2.2.1
            have p3329_3 := h3329c.2.2.2
            linarith only [hlam, p3329_0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h3606 | h3606
      · linarith only [h0, h1728, h1966, h2970, h3606, hc01, hc12, hlam, hphi]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3608 | h3608
        · linarith only [h1728, h1969, h2970, h3323, h3324, h3608, hc34, hlam, hphi, ht23, u2ehi3]
        · rcases h0bigk with h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c | h3610c
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [hlam, p3610_0]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h0, hlam, p3610_1]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1414, hlam, p3610_0]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1728, h2970, hc04, hc45, hlam, hphi, p3610_1]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1728, hlam, p3610_1]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            rcases p3610_3 (m.d 0 1) (by simp) with h3616 | h3616
            · linarith only [h0, h3616, hlam]
            · rcases p3610_3 (m.d 0 2) (by simp) with h3618 | h3618
              · rcases p3610_3 (m.d 0 3) (by simp) with h3619 | h3619
                · linarith only [h1965, h3619, hlam]
                · linarith only [h1414, h3619, hlam]
              · linarith only [h0, h3618, hlam]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [hlam, p3610_0]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h0, h1969, h3323, h3324, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3610_1, u2ehi3]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            rcases p3610_3 (m.d 0 1) (by simp) with h3625 | h3625
            · linarith only [h0, h3625, hlam]
            · rcases p3610_3 (m.d 0 2) (by simp) with h3627 | h3627
              · rcases p3610_3 (m.d 0 3) (by simp) with h3628 | h3628
                · linarith only [h1965, h3628, hlam]
                · linarith only [h1968, h3628, hlam]
              · linarith only [h1966, h3627, hlam]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h0, h1969, h3323, h3324, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3610_1, u2ehi3]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            rcases p3610_3 (m.d 0 1) (by simp) with h3633 | h3633
            · linarith only [h1414, h3633, hlam]
            · rcases p3610_3 (m.d 0 2) (by simp) with h3635 | h3635
              · rcases p3610_3 (m.d 0 3) (by simp) with h3636 | h3636
                · rcases p3610_3 (m.d 0 4) (by simp) with h3637 | h3637
                  · linarith only [h1968, h3637, hlam]
                  · rcases p3610_3 (m.d 0 5) (by simp) with h3639 | h3639
                    · linarith only [h1969, h3639, hlam]
                    · linarith only [h1728, h3639, hlam]
                · linarith only [h1414, h3636, hlam]
              · linarith only [h0, h3635, hlam]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1965, hlam, p3610_1]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [hlam, p3610_0]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            rcases p3610_3 (m.d 0 1) (by simp) with h3646 | h3646
            · linarith only [h1414, h3646, hlam]
            · rcases p3610_3 (m.d 0 2) (by simp) with h3648 | h3648
              · rcases p3610_3 (m.d 0 3) (by simp) with h3649 | h3649
                · rcases p3610_3 (m.d 0 4) (by simp) with h3650 | h3650
                  · linarith only [h1968, h3650, hlam]
                  · rcases p3610_3 (m.d 0 5) (by simp) with h3652 | h3652
                    · linarith only [h1969, h3652, hlam]
                    · linarith only [h1970, h3652, hlam]
                · linarith only [h1968, h3649, hlam]
              · linarith only [h1966, h3648, hlam]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1969, h3323, h3324, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3610_1, u2ehi3]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1970, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3610_1]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1966, hlam, p3610_0]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1968, hlam, p3610_0]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [hlam, p3610_0]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1970, hlam, p3610_0]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            rcases p3610_3 (m.d 0 1) (by simp) with h3663 | h3663
            · linarith only [h1728, h3663, hlam]
            · rcases p3610_3 (m.d 0 2) (by simp) with h3665 | h3665
              · rcases p3610_3 (m.d 0 3) (by simp) with h3666 | h3666
                · rcases p3610_3 (m.d 0 4) (by simp) with h3667 | h3667
                  · linarith only [h1970, h3667, hlam]
                  · linarith only [h1728, h1966, h2970, h3667, hc45, hlam, hphi, ht23, ht34, p3610_1, u2ehi3]
                · linarith only [h1414, h3666, hlam]
              · linarith only [h0, h3665, hlam]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1967, hlam, p3610_1]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1969, hlam, p3610_0]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [h1728, h1966, h2970, hc45, hlam, hphi, ht23, ht34, p3610_1, u2ehi3]
          · have p3610_0 := h3610c.1
            have p3610_1 := h3610c.2.1
            have p3610_2 := h3610c.2.2.1
            have p3610_3 := h3610c.2.2.2
            linarith only [hlam, p3610_0]
  · linarith only [h1968, h1970, h3323, hc45, hlam, hphi, ht23, ht34, u2ehi2]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x0_x0 (m : N7Model)
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
  rcases m.htr 1 4 5 (by decide) (by decide) with h2970 | h2970
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965 h2966 h2967 h2968 h2969 h2970
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965 h2966 h2967 h2968 h2969 h2970

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h2969 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  linarith only [h1414, h1969, h2969, hlam]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x0 (m : N7Model)
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h2969 | h2969
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965 h2966 h2967 h2968 h2969
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965 h2966 h2967 h2968 h2969

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x1 (m : N7Model)
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
    (h2968 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  linarith only [h1414, h1968, h1970, h2968, hc01, hc45, hlam, hphi, ht12, ht23, ht34]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0 (m : N7Model)
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
  rcases m.htr 1 3 4 (by decide) (by decide) with h2968 | h2968
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965 h2966 h2967 h2968
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965 h2966 h2967 h2968

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x1 (m : N7Model)
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
    (h2967 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  linarith only [h0, h1967, h2967, hlam]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0 (m : N7Model)
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h2967 | h2967
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965 h2966 h2967
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965 h2966 h2967

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x1 (m : N7Model)
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
    (h2966 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  linarith only [h0, h1965, h2966, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0 (m : N7Model)
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h2966 | h2966
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965 h2966
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965 h2966

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x1 (m : N7Model)
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
    (h2965 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  linarith only [h0, h1966, h2965, hc23, hlam, hphi, u2ehi3]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1 (m : N7Model)
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h2965 | h2965
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h2965

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0 (m : N7Model)
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h1970 | h1970
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970

end R2N4
