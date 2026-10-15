import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2875 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3145 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h3146 | h3146
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3147 | h3147
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3148 | h3148
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3149 | h3149
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3150 | h3150
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3151 | h3151
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3152 | h3152
              · rcases h0bigk with h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c | h3153c
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [hlam, p3153_0]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h0, hlam, p3153_1]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h2352, hlam, p3153_0]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h2875, hlam, p3153_1]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h2994, hlam, p3153_1]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3153_1]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [hlam, p3153_0]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h0, h3148, h3150, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3153_1, u4ehi4]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h0, h3150, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3153_1, u4ehi4]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h0, h3150, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3153_1, u4ehi4]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h2352, h3151, hc01, hc12, hlam, hphi, p3153_1]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h3145, hlam, p3153_1]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [hlam, p3153_0]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h2352, h3150, h3151, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3153_1, u4ehi4]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h2352, h3150, h3151, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3153_1, u4ehi4]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h2875, hc01, hc14, hlam, hphi, p3153_1]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h3146, hlam, p3153_0]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h3148, hlam, p3153_0]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [hlam, p3153_0]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h2352, h3148, h3150, h3151, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3153_1, u4ehi4]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h2994, hc01, hc15, hlam, hphi, p3153_1]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h3147, hlam, p3153_1]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h3149, hlam, p3153_0]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [h3150, hlam, p3153_1]
                · have p3153_0 := h3153c.1
                  have p3153_1 := h3153c.2.1
                  have p3153_2 := h3153c.2.2.1
                  have p3153_3 := h3153c.2.2.2
                  linarith only [hlam, p3153_0]
              · linarith only [h2875, h3150, h3152, hlam]
            · linarith only [h0, h3145, h3151, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3181 | h3181
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3182 | h3182
              · rcases h0bigk with h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [hlam, p3183_0]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h0, hlam, p3183_1]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h2352, hlam, p3183_0]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h2875, hlam, p3183_1]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h2994, hlam, p3183_1]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3183_1]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [hlam, p3183_0]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h0, h3148, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3183_1, u4ehi3]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h0, h3146, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3183_1, u4ehi2]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h0, h3146, h3150, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3183_1, u4ehi2]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h2352, hc01, hc13, hlam, hphi, p3183_1]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h3145, hlam, p3183_1]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [hlam, p3183_0]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h0, h3145, h3146, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3183_1, u4ehi2]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h0, h3145, h3146, h3150, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3183_1, u4ehi2]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h3150, h3182, hc01, hc14, hlam, hphi, p3183_1]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h3146, hlam, p3183_0]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h3148, hlam, p3183_0]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [hlam, p3183_0]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h3150, hlam, p3183_0]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h2994, h3182, hc01, hc14, hlam, hphi, p3183_1]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h3147, hlam, p3183_1]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h3149, hlam, p3183_0]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [h3150, h3182, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3183_1, u4ehi0]
                · have p3183_0 := h3183c.1
                  have p3183_1 := h3183c.2.1
                  have p3183_2 := h3183c.2.2.1
                  have p3183_3 := h3183c.2.2.2
                  linarith only [hlam, p3183_0]
              · rcases h0bigk with h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c | h3209c
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [hlam, p3209_0]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h0, hlam, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h2352, hlam, p3209_0]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h2875, hlam, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h2994, hlam, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [hlam, p3209_0]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h0, h3149, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h0, h3146, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3209_1, u4ehi2]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h0, h2994, hc01, hc12, hlam, hphi, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h2352, h3181, hc01, hc12, hlam, hphi, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h3145, hlam, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [hlam, p3209_0]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h2352, h3146, h3181, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3209_1, u4ehi2]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h2352, h2994, h3181, hc01, hc12, hlam, hphi, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h2875, h3182, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h3146, hlam, p3209_0]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h3148, hlam, p3209_0]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [hlam, p3209_0]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h3150, hlam, p3209_0]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h2994, h3182, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h3147, hlam, p3209_1]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h3149, hlam, p3209_0]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [h2994, h3182, hc45, hlam, hphi, p3209_1, u4ehi0]
                · have p3209_0 := h3209c.1
                  have p3209_1 := h3209c.2.1
                  have p3209_2 := h3209c.2.2.1
                  have p3209_3 := h3209c.2.2.2
                  linarith only [hlam, p3209_0]
            · linarith only [h0, h3145, h3181, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3236 | h3236
          · linarith only [h3148, h3149, h3236, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3238 | h3238
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3239 | h3239
              · rcases h0bigk with h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c | h3240c
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [hlam, p3240_0]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h0, hlam, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h2352, hlam, p3240_0]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h2875, hlam, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h2994, hlam, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [hlam, p3240_0]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h0, h2352, hc01, hc12, hlam, hphi, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3240_1, u4ehi0]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h0, h2352, h3149, hc01, hc12, hlam, hphi, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h2352, hc01, hc13, hlam, hphi, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h3145, hlam, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [hlam, p3240_0]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h0, h3146, h3147, h3149, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3240_1, u4ehi2]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h3149, hlam, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h2875, hc01, hc14, hlam, hphi, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h3146, hlam, p3240_0]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h3148, hlam, p3240_0]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [hlam, p3240_0]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h3236, hlam, p3240_0]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h0, h3147, hc01, hc12, hlam, hphi, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h3147, hlam, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h0, h2352, h3147, hc01, hc12, hlam, hphi, p3240_1]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [h3236, h3239, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3240_1, u4ehi0]
                · have p3240_0 := h3240c.1
                  have p3240_1 := h3240c.2.1
                  have p3240_2 := h3240c.2.2.1
                  have p3240_3 := h3240c.2.2.2
                  linarith only [hlam, p3240_0]
              · rcases h0bigk with h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [hlam, p3266_0]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h0, hlam, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h2352, hlam, p3266_0]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h2875, hlam, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h2994, hlam, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [hlam, p3266_0]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h0, h3148, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3266_1, u4ehi3]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h0, h3146, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3266_1, u4ehi2]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h0, h2994, hc01, hc12, hlam, hphi, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h2352, h3238, hc01, hc12, hlam, hphi, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h3145, hlam, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [hlam, p3266_0]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h2352, h3146, h3238, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3266_1, u4ehi2]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h3149, hlam, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h2875, h3239, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h3146, hlam, p3266_0]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h3148, hlam, p3266_0]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [hlam, p3266_0]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h3236, hlam, p3266_0]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h2994, h3239, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h3147, hlam, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h2994, h3239, hc03, hc45, hlam, hphi, ht34, p3266_1]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [h2994, h3239, hc45, hlam, hphi, p3266_1, u4ehi0]
                · have p3266_0 := h3266c.1
                  have p3266_1 := h3266c.2.1
                  have p3266_2 := h3266c.2.2.1
                  have p3266_3 := h3266c.2.2.2
                  linarith only [hlam, p3266_0]
            · linarith only [h0, h3145, h3238, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3293 | h3293
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3294 | h3294
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3295 | h3295
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3296 | h3296
              · rcases h0bigk with h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c | h3297c
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [hlam, p3297_0]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h0, hlam, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h2352, hlam, p3297_0]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h2875, hlam, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h2994, hlam, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [hlam, p3297_0]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h0, h3293, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3297_1, u4ehi0]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h0, h2994, hc01, hc12, hlam, hphi, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h2352, hc01, hc13, hlam, hphi, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h3145, hlam, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [hlam, p3297_0]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h3148, hlam, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h2994, h3148, hc01, hc34, hlam, hphi, ht12, ht23, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h2875, hc01, hc14, hlam, hphi, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h3146, hlam, p3297_0]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h3148, hc03, hc34, hlam, hphi, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [hlam, p3297_0]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h2994, h3148, hc01, hc34, hlam, hphi, ht12, ht23, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h2994, h3296, hc01, hc14, hlam, hphi, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h3147, hlam, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h3293, hlam, p3297_0]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [h3294, hlam, p3297_1]
                · have p3297_0 := h3297c.1
                  have p3297_1 := h3297c.2.1
                  have p3297_2 := h3297c.2.2.1
                  have p3297_3 := h3297c.2.2.2
                  linarith only [hlam, p3297_0]
              · linarith only [h2875, h3294, h3296, hlam]
            · linarith only [h0, h3145, h3295, hlam]
          · linarith only [h3148, h3293, h3294, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3326 | h3326
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3327 | h3327
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3328 | h3328
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
                  linarith only [h2352, hlam, p3329_0]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h2875, hlam, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h2994, hlam, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [hlam, p3329_0]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h0, h2352, hc01, hc12, hlam, hphi, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h0, h3326, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3329_1, u4ehi4]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h0, h2994, hc01, hc12, hlam, hphi, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h3148, hc01, hc34, hlam, hphi, ht12, ht23, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h3145, hlam, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [hlam, p3329_0]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h3148, hlam, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h3293, hlam, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h2875, hc01, hc14, hlam, hphi, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h3146, hlam, p3329_0]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h3148, hc03, hc34, hlam, hphi, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [hlam, p3329_0]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h2352, h3148, h3293, hc01, hc34, hlam, hphi, ht12, ht23, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h2994, h3328, hc01, hc14, hlam, hphi, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h3147, hlam, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h2352, h3293, hc01, hc35, hlam, hphi, ht12, ht23, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [h3326, hlam, p3329_1]
                · have p3329_0 := h3329c.1
                  have p3329_1 := h3329c.2.1
                  have p3329_2 := h3329c.2.2.1
                  have p3329_3 := h3329c.2.2.2
                  linarith only [hlam, p3329_0]
              · linarith only [h2875, h3326, h3328, hlam]
            · linarith only [h0, h3145, h3327, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3357 | h3357
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3358 | h3358
              · rcases h0bigk with h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [hlam, p3359_0]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h0, hlam, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h2352, hlam, p3359_0]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h2875, hlam, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h2994, hlam, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [hlam, p3359_0]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h0, h2352, hc01, hc12, hlam, hphi, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h0, h3146, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3359_1, u4ehi2]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h0, h3146, h3326, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3359_1, u4ehi2]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h2352, h3357, hc01, hc12, hlam, hphi, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h3145, hlam, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [hlam, p3359_0]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h3148, hlam, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h3293, hlam, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h3326, h3358, hc01, hc14, hlam, hphi, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h3146, hlam, p3359_0]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h3326, h3358, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [hlam, p3359_0]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h3326, hlam, p3359_0]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h2994, h3358, hc01, hc14, hlam, hphi, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h3147, hlam, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h2352, h3293, hc01, hc35, hlam, hphi, ht12, ht23, p3359_1]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [h3326, h3358, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3359_1, u4ehi0]
                · have p3359_0 := h3359c.1
                  have p3359_1 := h3359c.2.1
                  have p3359_2 := h3359c.2.2.1
                  have p3359_3 := h3359c.2.2.2
                  linarith only [hlam, p3359_0]
              · rcases h0bigk with h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c | h3385c
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [hlam, p3385_0]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h0, hlam, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h2352, hlam, p3385_0]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h2875, hlam, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h2994, hlam, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [hlam, p3385_0]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h0, h2352, hc01, hc12, hlam, hphi, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h0, h3146, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3385_1, u4ehi2]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h0, h2994, hc01, hc12, hlam, hphi, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h2352, h3357, hc01, hc12, hlam, hphi, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h3145, hlam, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [hlam, p3385_0]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h3148, hlam, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h3293, hlam, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h2875, h3358, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h3146, hlam, p3385_0]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h2875, h3358, hc03, hc45, hlam, hphi, ht34, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [hlam, p3385_0]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h3326, hlam, p3385_0]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h2994, h3358, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h3147, hlam, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h2352, h2994, h3358, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3385_1]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [h2994, h3358, hc45, hlam, hphi, p3385_1, u4ehi0]
                · have p3385_0 := h3385c.1
                  have p3385_1 := h3385c.2.1
                  have p3385_2 := h3385c.2.2.1
                  have p3385_3 := h3385c.2.2.2
                  linarith only [hlam, p3385_0]
            · linarith only [h0, h3145, h3357, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3412 | h3412
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3413 | h3413
        · linarith only [h3145, h3147, h3413, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3415 | h3415
          · linarith only [h3145, h3147, h3412, h3415, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3417 | h3417
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3418 | h3418
              · rcases h0bigk with h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [hlam, p3419_0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h0, hlam, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h2352, hlam, p3419_0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h2875, hlam, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h2994, hlam, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3147, h3415, h3418, hc01, hc14, hlam, hphi, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [hlam, p3419_0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3147, h3415, h3418, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3147, h3415, h3418, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3419_1, u4ehi0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3147, hlam, p3419_0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3413, hc01, hc35, hlam, hphi, ht12, ht23, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3145, hlam, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [hlam, p3419_0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3145, h3146, h3147, h3415, h3418, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3419_1, u4ehi2]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3413, hlam, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h2875, hc01, hc14, hlam, hphi, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3146, hlam, p3419_0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3412, hlam, p3419_0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [hlam, p3419_0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3415, hlam, p3419_0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3415, h3418, hc01, hc14, hlam, hphi, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3415, h3418, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3419_1]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3412, h3415, h3418, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3419_1, u4ehi3]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [h3415, h3418, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3419_1, u4ehi0]
                · have p3419_0 := h3419c.1
                  have p3419_1 := h3419c.2.1
                  have p3419_2 := h3419c.2.2.1
                  have p3419_3 := h3419c.2.2.2
                  linarith only [hlam, p3419_0]
              · rcases h0bigk with h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [hlam, p3445_0]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h0, hlam, p3445_1]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h2352, hlam, p3445_0]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h2875, hlam, p3445_1]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h2994, hlam, p3445_1]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h3147, hc01, hc25, hlam, hphi, ht12, p3445_1]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [hlam, p3445_0]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h3147, h3412, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3445_1, u4ehi3]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h3146, h3147, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3445_1, u4ehi2]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h3147, hlam, p3445_0]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h2352, h3417, hc01, hc12, hlam, hphi, p3445_1]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h3145, hlam, p3445_1]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [hlam, p3445_0]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h3145, h3146, h3147, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3445_1, u4ehi2]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h3413, hlam, p3445_1]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h2875, h3418, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3445_1]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h3146, hlam, p3445_0]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h3412, hlam, p3445_0]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [hlam, p3445_0]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h3415, hlam, p3445_0]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h2994, h3418, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3445_1]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h2994, h3418, hc02, hc45, hlam, hphi, ht23, ht34, p3445_1]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h2994, h3412, h3418, hc45, hlam, hphi, p3445_1, u4ehi3]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [h2994, h3418, hc45, hlam, hphi, p3445_1, u4ehi0]
                · have p3445_0 := h3445c.1
                  have p3445_1 := h3445c.2.1
                  have p3445_2 := h3445c.2.2.1
                  have p3445_3 := h3445c.2.2.2
                  linarith only [hlam, p3445_0]
            · linarith only [h0, h3145, h3417, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3472 | h3472
        · linarith only [h3146, h3147, h3412, h3472, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3474 | h3474
          · linarith only [h3146, h3147, h3474, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3476 | h3476
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3477 | h3477
              · rcases h0bigk with h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c | h3478c
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [hlam, p3478_0]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h0, hlam, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h2352, hlam, p3478_0]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h2875, hlam, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h2994, hlam, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [hlam, p3478_0]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h2352, h2994, h3147, hc01, hc15, hlam, hphi, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h2994, h3147, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p3478_1, u4ehi0]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3147, hlam, p3478_0]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3412, hc01, hc34, hlam, hphi, ht12, ht23, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3145, hlam, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [hlam, p3478_0]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3412, hlam, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3472, hlam, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h2875, hc01, hc14, hlam, hphi, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3146, hlam, p3478_0]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3146, h3147, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [hlam, p3478_0]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3474, hlam, p3478_0]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3147, hc01, hc25, hlam, hphi, ht12, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3147, hc02, hc25, hlam, hphi, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h2352, h3472, hc01, hc35, hlam, hphi, ht12, ht23, p3478_1]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [h3146, h3474, h3477, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3478_1, u4ehi2]
                · have p3478_0 := h3478c.1
                  have p3478_1 := h3478c.2.1
                  have p3478_2 := h3478c.2.2.1
                  have p3478_3 := h3478c.2.2.2
                  linarith only [hlam, p3478_0]
              · rcases h0bigk with h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h0, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2352, hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2875, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2994, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h0, h2352, hc01, hc12, hlam, hphi, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h0, h3146, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3504_1, u4ehi2]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3147, hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2352, hc01, hc13, hlam, hphi, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3145, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3412, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3472, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2875, hc01, hc14, hlam, hphi, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3146, hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2875, h3477, hc03, hc45, hlam, hphi, ht34, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3474, hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2994, hc01, hc15, hlam, hphi, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3147, hc02, hc25, hlam, hphi, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2352, h3472, hc01, hc35, hlam, hphi, ht12, ht23, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3474, hc45, hlam, hphi, p3504_1, u4ehi0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [hlam, p3504_0]
            · linarith only [h0, h3145, h3476, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3531 | h3531
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3532 | h3532
      · linarith only [h3145, h3146, h3532, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3534 | h3534
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3535 | h3535
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3536 | h3536
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3537 | h3537
              · rcases h0bigk with h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [hlam, p3538_0]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h0, hlam, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h2352, hlam, p3538_0]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h2875, hlam, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h2994, hlam, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [hlam, p3538_0]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3146, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3146, hlam, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3146, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3532, hc01, hc34, hlam, hphi, ht12, ht23, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3145, hlam, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [hlam, p3538_0]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3532, hlam, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h2994, h3532, hc01, hc34, hlam, hphi, ht12, ht23, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h2875, hc01, hc14, hlam, hphi, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3146, hc02, hc24, hlam, hphi, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3532, hc03, hc34, hlam, hphi, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [hlam, p3538_0]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h2994, h3532, hc01, hc34, hlam, hphi, ht12, ht23, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h2994, h3537, hc01, hc14, hlam, hphi, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3531, hlam, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3534, hlam, p3538_0]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [h3535, hlam, p3538_1]
                · have p3538_0 := h3538c.1
                  have p3538_1 := h3538c.2.1
                  have p3538_2 := h3538c.2.2.1
                  have p3538_3 := h3538c.2.2.2
                  linarith only [hlam, p3538_0]
              · linarith only [h2875, h3145, h3146, h3534, h3535, h3537, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h3145, h3536, hlam]
          · linarith only [h3145, h3146, h3534, h3535, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3567 | h3567
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3568 | h3568
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3569 | h3569
              · rcases h0bigk with h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c | h3570c
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [hlam, p3570_0]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h0, hlam, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2352, hlam, p3570_0]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2875, hlam, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2994, hlam, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [hlam, p3570_0]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2352, h2875, h3146, hc01, hc14, hlam, hphi, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h3146, hlam, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2875, h2994, h3146, hc01, hc14, hlam, hphi, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2352, hc01, hc13, hlam, hphi, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h3145, hlam, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [hlam, p3570_0]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h3532, hlam, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h3534, hlam, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2875, hc01, hc14, hlam, hphi, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2875, h3531, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h3532, hc03, hc34, hlam, hphi, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [hlam, p3570_0]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2352, h3532, h3534, hc01, hc34, hlam, hphi, ht12, ht23, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2994, h3569, hc01, hc14, hlam, hphi, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h3531, hlam, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h2352, h3146, h3531, hc01, hc24, hlam, hphi, ht12, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [h3567, hlam, p3570_1]
                · have p3570_0 := h3570c.1
                  have p3570_1 := h3570c.2.1
                  have p3570_2 := h3570c.2.2.1
                  have p3570_3 := h3570c.2.2.2
                  linarith only [hlam, p3570_0]
              · linarith only [h2875, h3532, h3567, h3569, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h3145, h3568, hlam]
          · linarith only [h3146, h3531, h3567, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3599 | h3599
      · linarith only [h3145, h3146, h3599, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3601 | h3601
        · linarith only [h3145, h3531, h3601, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3603 | h3603
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3604 | h3604
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3605 | h3605
              · rcases h0bigk with h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c | h3606c
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [hlam, p3606_0]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h0, hlam, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h2352, hlam, p3606_0]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h2875, hlam, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h2994, hlam, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h2875, h3531, h3603, hc01, hc14, hlam, hphi, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [hlam, p3606_0]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h3531, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h3146, hlam, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h3531, hlam, p3606_0]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h3599, hc01, hc34, hlam, hphi, ht12, ht23, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h3145, hlam, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [hlam, p3606_0]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h3599, hlam, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h3601, hlam, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h2875, hc01, hc14, hlam, hphi, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h3146, hc02, hc24, hlam, hphi, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h3599, hc03, hc34, hlam, hphi, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [hlam, p3606_0]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h2994, h3599, hc01, hc34, hlam, hphi, ht12, ht23, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h2994, h3605, hc01, hc14, hlam, hphi, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h2994, h3145, h3605, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h2352, h3601, hc01, hc35, hlam, hphi, ht12, ht23, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [h3603, hlam, p3606_1]
                · have p3606_0 := h3606c.1
                  have p3606_1 := h3606c.2.1
                  have p3606_2 := h3606c.2.2.1
                  have p3606_3 := h3606c.2.2.2
                  linarith only [hlam, p3606_0]
              · linarith only [h2875, h3599, h3603, h3605, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h3145, h3604, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3634 | h3634
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3635 | h3635
              · rcases h0bigk with h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [hlam, p3636_0]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h0, hlam, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h2352, hlam, p3636_0]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h2875, hlam, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h2994, hlam, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3146, h3603, h3635, hc01, hc14, hlam, hphi, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [hlam, p3636_0]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h2352, h3146, h3603, h3635, hc01, hc14, hlam, hphi, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3146, hlam, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3531, hlam, p3636_0]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h2352, hc01, hc13, hlam, hphi, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3145, hlam, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [hlam, p3636_0]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3599, hlam, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3601, hlam, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3603, h3635, hc01, hc14, hlam, hphi, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3603, h3635, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3603, h3635, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [hlam, p3636_0]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3603, hlam, p3636_0]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3603, h3635, hc01, hc14, hlam, hphi, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3145, h3603, h3635, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h2352, h3603, h3635, hc01, hc14, hlam, hphi, p3636_1]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [h3603, h3635, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3636_1, u4ehi0]
                · have p3636_0 := h3636c.1
                  have p3636_1 := h3636c.2.1
                  have p3636_2 := h3636c.2.2.1
                  have p3636_3 := h3636c.2.2.2
                  linarith only [hlam, p3636_0]
              · rcases h0bigk with h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c | h3662c
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [hlam, p3662_0]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h0, hlam, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2352, hlam, p3662_0]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2875, hlam, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2994, hlam, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [hlam, p3662_0]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h0, h2352, hc01, hc12, hlam, hphi, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h3146, hlam, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h3531, hlam, p3662_0]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2352, h3634, hc01, hc12, hlam, hphi, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h3145, hlam, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [hlam, p3662_0]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h3599, hlam, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h3601, hlam, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2875, h3635, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2875, h3635, hc02, hc45, hlam, hphi, ht23, ht34, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2352, h2875, h3635, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [hlam, p3662_0]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h3603, hlam, p3662_0]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2994, h3635, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2994, h3145, h3635, hc23, hc45, hlam, hphi, ht34, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2352, h2994, h3635, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3662_1]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [h2994, h3635, hc45, hlam, hphi, p3662_1, u4ehi0]
                · have p3662_0 := h3662c.1
                  have p3662_1 := h3662c.2.1
                  have p3662_2 := h3662c.2.2.1
                  have p3662_3 := h3662c.2.2.2
                  linarith only [hlam, p3662_0]
            · linarith only [h0, h3145, h3634, hlam]

end R2N4
