import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2875 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2994 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2995 | h2995
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2996 | h2996
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2997 | h2997
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2998 | h2998
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2999 | h2999
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3000 | h3000
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3001 | h3001
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3002 | h3002
                · rcases h0bigk with h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [hlam, p3003_0]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h0, hlam, p3003_1]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2352, hlam, p3003_0]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2875, hlam, p3003_1]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2352, h3001, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3003_1]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2994, hc02, hc15, hlam, hphi, ht0b, ht5b, p3003_1]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [hlam, p3003_0]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h0, h2352, h2994, h3002, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3003_1, u4ehi4]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h0, h2875, h2994, h3002, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3003_1, u4ehi4]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h0, h2994, h3002, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3003_1, u4ehi4]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2994, h3002, hc03, hlam, hphi, ht0b, ht45, ht5b, p3003_1, u4ehi4]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2995, hlam, p3003_1]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [hlam, p3003_0]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h0, h2875, h2994, h2995, h3002, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3003_1, u4ehi4]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h0, h2994, h2995, h3002, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3003_1, u4ehi4]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2994, h3002, hc04, hlam, hphi, ht0b, ht45, ht5b, p3003_1, u4ehi4]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2996, hlam, p3003_0]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2998, hlam, p3003_0]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [hlam, p3003_0]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h0, h2994, h2995, h2998, h3002, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3003_1, u4ehi4]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2994, hlam, p3003_0]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2997, hlam, p3003_1]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h2999, hlam, p3003_0]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [h3000, hlam, p3003_1]
                  · have p3003_0 := h3003c.1
                    have p3003_1 := h3003c.2.1
                    have p3003_2 := h3003c.2.2.1
                    have p3003_3 := h3003c.2.2.2
                    linarith only [hlam, p3003_0]
                · linarith only [h2875, h3000, h3002, hlam]
              · linarith only [h0, h2995, h3001, hlam]
            · linarith only [h2875, h2994, h3000, hlam]
          · linarith only [h2352, h2994, h2999, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3033 | h3033
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3034 | h3034
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3035 | h3035
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3036 | h3036
                · rcases h0bigk with h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [hlam, p3037_0]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h0, hlam, p3037_1]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2352, hlam, p3037_0]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2875, hlam, p3037_1]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2875, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p3037_1]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h0, h2994, h3036, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3037_1, u4ehi4]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [hlam, p3037_0]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h0, h3033, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3037_1]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h0, h2875, h2994, h3036, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3037_1, u4ehi4]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h0, h2994, h3036, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3037_1, u4ehi4]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2994, h2998, h3036, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3037_1, u4ehi4]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2995, hlam, p3037_1]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [hlam, p3037_0]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2998, hlam, p3037_1]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2994, h2998, h3036, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3037_1, u4ehi4]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2994, h3036, hc04, hlam, hphi, ht0b, ht45, ht5b, p3037_1, u4ehi4]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2996, hlam, p3037_0]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2998, hc03, hc34, hlam, hphi, p3037_1]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [hlam, p3037_0]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2994, h2998, h3036, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3037_1, u4ehi4]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2994, hlam, p3037_0]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h2997, hlam, p3037_1]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h3033, hlam, p3037_0]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [h3034, hlam, p3037_1]
                  · have p3037_0 := h3037c.1
                    have p3037_1 := h3037c.2.1
                    have p3037_2 := h3037c.2.2.1
                    have p3037_3 := h3037c.2.2.2
                    linarith only [hlam, p3037_0]
                · linarith only [h2875, h3034, h3036, hlam]
              · linarith only [h0, h2995, h3035, hlam]
            · linarith only [h2352, h2994, h2998, h3034, hlam]
          · linarith only [h2352, h2994, h3033, hlam]
      · linarith only [h0, h2994, h2997, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3068 | h3068
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3069 | h3069
        · linarith only [h2995, h2996, h3069, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3071 | h3071
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3072 | h3072
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3073 | h3073
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3074 | h3074
                · rcases h0bigk with h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [hlam, p3075_0]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h0, hlam, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2352, hlam, p3075_0]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2875, hlam, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2875, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2994, h2996, h3074, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3075_1, u4ehi4]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [hlam, p3075_0]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2996, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2996, hlam, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2994, h2996, h3074, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3075_1, u4ehi4]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2994, h3069, h3074, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3075_1, u4ehi4]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2995, hlam, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [hlam, p3075_0]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h3069, hlam, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2994, h3069, h3074, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3075_1, u4ehi4]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2994, h3074, hc04, hlam, hphi, ht0b, ht45, ht5b, p3075_1, u4ehi4]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2996, hc02, hc24, hlam, hphi, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h3069, hc03, hc34, hlam, hphi, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [hlam, p3075_0]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2994, h3069, h3074, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3075_1, u4ehi4]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h2994, hlam, p3075_0]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h3068, hlam, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h3071, hlam, p3075_0]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [h3072, hlam, p3075_1]
                  · have p3075_0 := h3075c.1
                    have p3075_1 := h3075c.2.1
                    have p3075_2 := h3075c.2.2.1
                    have p3075_3 := h3075c.2.2.2
                    linarith only [hlam, p3075_0]
                · linarith only [h2875, h3072, h3074, hlam]
              · linarith only [h0, h2994, h2995, h3073, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h2994, h2996, h3072, hlam]
          · linarith only [h2352, h2994, h3071, hlam]
      · linarith only [h2352, h2994, h2995, h3068, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3106 | h3106
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3107 | h3107
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3108 | h3108
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3109 | h3109
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3110 | h3110
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3111 | h3111
              · linarith only [h2995, h3106, h3111, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3113 | h3113
                · linarith only [h0, h2994, h3111, h3113, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h2875, h2994, h3106, h3110, h3113, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h2875, h2994, h3110, hlam]
          · linarith only [h0, h2994, h2995, h3109, hlam]
        · linarith only [h2995, h3106, h3108, hlam]
      · linarith only [h0, h2994, h3107, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3120 | h3120
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3121 | h3121
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3122 | h3122
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3123 | h3123
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3124 | h3124
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3125 | h3125
                · linarith only [h0, h2994, h2995, h3124, h3125, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h2875, h2994, h3121, h3123, h3125, hc03, hc15, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3128 | h3128
                · linarith only [h0, h2994, h3124, h3128, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h2875, h2994, h3123, h3128, hlam]
            · linarith only [h0, h2994, h3106, h3123, hlam]
          · linarith only [h2352, h2994, h3122, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3133 | h3133
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3134 | h3134
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3135 | h3135
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3136 | h3136
                · linarith only [h0, h2994, h2995, h3135, h3136, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h2875, h2994, h3134, h3136, hc04, hc15, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3139 | h3139
                · linarith only [h0, h2994, h3135, h3139, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h2875, h2994, h3134, h3139, hlam]
            · linarith only [h0, h2994, h2995, h3121, h3134, hlam]
          · linarith only [h0, h2994, h2995, h3133, hlam]
      · linarith only [h0, h2994, h3120, hlam]

end R2N4
