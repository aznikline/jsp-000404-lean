import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
          · rcases h1bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p10_1, u5ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h7, h9, hc01, hlam, hphi, ht0b, ht5b, p10_1, u5ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h9, hc01, hlam, hphi, ht0b, ht5b, p10_1, u5ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p10_1, u5ehi1]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h0, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h7, h9, hc12, hlam, hphi, ht01, ht0b, ht5b, p10_1, u5ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht5b, p10_1, u5ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p10_1, u5ehi1]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h1, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h4, hlam, p10_1]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h9, hc13, hlam, hphi, ht01, ht0b, ht5b, p10_1, u5ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht5b, p10_1, u5ehi2]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h2, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h5, hlam, p10_1]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h7, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h6, hc14, hlam, hphi, ht01, ht0b, ht5b, p10_1, u5ehi2]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h3, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h6, hlam, p10_1]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h8, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h9, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hlam, p10_0]
          · rcases h1bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              rcases p36_3 (m.d 0 1) (by simp) with h40 | h40
              · rcases p36_3 (m.d 1 2) (by simp) with h41 | h41
                · linarith only [h0, h41, hlam]
                · linarith only [h41, h5, hlam]
              · linarith only [h40, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h6, hc01, hlam, hphi, ht0b, ht5b, p36_1, u5ehi2]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h0, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h8, hc12, hlam, hphi, ht01, ht0b, ht5b, p36_1, u5ehi3]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht5b, p36_1, u5ehi2]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h1, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h4, hlam, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h1, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht5b, p36_1, u5ehi2]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h2, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h5, hlam, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h7, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h9, hlam, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h3, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h6, hlam, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h8, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h3, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [hlam, p36_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
          · linarith only [h66, h7, h8, hlam]
          · rcases h1bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [hlam, p68_0]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              rcases p68_3 (m.d 0 1) (by simp) with h72 | h72
              · rcases p68_3 (m.d 1 2) (by simp) with h73 | h73
                · linarith only [h0, h73, hlam]
                · linarith only [h5, h73, hlam]
              · linarith only [h72, hlam, p68_0]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h0, hlam, p68_0]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [hlam, p68_0]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h7, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h0, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h1, hlam, p68_0]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h4, hlam, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [hlam, p68_0]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h1, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h8, hlam, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h2, hlam, p68_0]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h5, hlam, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h7, hlam, p68_0]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [hlam, p68_0]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h66, hlam, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h3, hlam, p68_0]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h6, hlam, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [h0, h5, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p68_1]
            · have p68_0 := h68c.1
              have p68_1 := h68c.2.1
              have p68_2 := h68c.2.2.1
              have p68_3 := h68c.2.2.2
              linarith only [hlam, p68_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
        · rcases m.htr 1 4 5 (by decide) (by decide) with h99 | h99
          · rcases h1bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [hlam, p100_0]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h98, hc01, hlam, hphi, ht0b, ht5b, p100_1, u5ehi3]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h7, h98, hc01, hlam, hphi, ht0b, ht5b, p100_1, u5ehi3]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p100_1, u5ehi1]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h0, hlam, p100_0]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [hlam, p100_0]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h98, hc12, hlam, hphi, ht01, ht0b, ht5b, p100_1, u5ehi3]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h0, h7, h98, hc01, hlam, hphi, ht0b, ht5b, p100_1, u5ehi3]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p100_1, u5ehi1]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h1, hlam, p100_0]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h4, hlam, p100_1]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [hlam, p100_0]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h7, hlam, p100_1]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h6, hc13, hlam, hphi, ht01, ht0b, ht5b, p100_1, u5ehi2]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h2, hlam, p100_0]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h5, hlam, p100_1]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [hlam, p100_0]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h0, h5, h6, hc01, hlam, hphi, ht0b, ht5b, p100_1, u5ehi2]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h3, hlam, p100_0]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h6, hlam, p100_1]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h98, hlam, p100_0]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [h99, hlam, p100_0]
            · have p100_0 := h100c.1
              have p100_1 := h100c.2.1
              have p100_2 := h100c.2.2.1
              have p100_3 := h100c.2.2.2
              linarith only [hlam, p100_0]
          · linarith only [h7, h98, h99, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h127 | h127
          · rcases h1bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [hlam, p128_0]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h127, h5, hc01, hlam, hphi, ht0b, ht5b, p128_1, u5ehi4]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              rcases p128_3 (m.d 0 1) (by simp) with h131 | h131
              · rcases p128_3 (m.d 1 2) (by simp) with h132 | h132
                · linarith only [h0, h132, hlam]
                · linarith only [h132, h4, hlam]
              · linarith only [h131, hlam, p128_0]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h127, hc01, hlam, hphi, ht0b, ht5b, p128_1, u5ehi1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p128_1, u5ehi1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h0, hlam, p128_0]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [hlam, p128_0]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h0, h127, hc01, hlam, hphi, ht0b, ht5b, p128_1, u5ehi1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p128_1, u5ehi1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h1, hlam, p128_0]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h4, hlam, p128_1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [hlam, p128_0]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h7, hlam, p128_1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h98, hlam, p128_1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h2, hlam, p128_0]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h5, hlam, p128_1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h4, h7, hc23, hc34, hlam, hphi, p128_1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [hlam, p128_0]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h0, h5, h6, hc01, hlam, hphi, ht0b, ht5b, p128_1, u5ehi2]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h3, hlam, p128_0]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h6, hlam, p128_1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [h127, hlam, p128_0]
            · have p128_0 := h128c.1
              have p128_1 := h128c.2.1
              have p128_2 := h128c.2.2.1
              have p128_3 := h128c.2.2.2
              linarith only [hlam, p128_0]
          · rcases h1bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [hlam, p158_0]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h6, hc01, hlam, hphi, ht0b, ht5b, p158_1, u5ehi1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              rcases p158_3 (m.d 0 1) (by simp) with h161 | h161
              · rcases p158_3 (m.d 1 2) (by simp) with h162 | h162
                · linarith only [h0, h162, hlam]
                · linarith only [h162, h4, hlam]
              · linarith only [h161, hlam, p158_0]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              rcases p158_3 (m.d 0 1) (by simp) with h166 | h166
              · rcases p158_3 (m.d 1 2) (by simp) with h167 | h167
                · linarith only [h0, h167, hlam]
                · linarith only [h167, h5, hlam]
              · linarith only [h166, hlam, p158_0]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p158_1, u5ehi1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h0, hlam, p158_0]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [hlam, p158_0]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p158_1, u5ehi1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h1, hlam, p158_0]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h4, hlam, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [hlam, p158_0]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h7, hlam, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h98, hlam, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h2, hlam, p158_0]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h5, hlam, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [hlam, p158_0]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h127, hlam, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h3, hlam, p158_0]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h6, hlam, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [h0, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p158_1]
            · have p158_0 := h158c.1
              have p158_1 := h158c.2.1
              have p158_2 := h158c.2.2.1
              have p158_3 := h158c.2.2.2
              linarith only [hlam, p158_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
      · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
        · linarith only [h193, h4, h6, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
          · linarith only [h192, h195, h4, h6, hlam]
          · rcases h1bigk with h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h192, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              rcases p197_3 (m.d 0 1) (by simp) with h201 | h201
              · rcases p197_3 (m.d 1 2) (by simp) with h202 | h202
                · linarith only [h0, h202, hlam]
                · linarith only [h202, h5, hlam]
              · linarith only [h201, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h0, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h192, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h6, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h1, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h4, hlam, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h193, h5, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h193, hlam, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h2, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h5, hlam, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h192, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h195, hlam, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h3, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h3, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [hlam, p197_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
        · linarith only [h192, h227, h5, h6, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
          · linarith only [h229, h5, h6, hlam]
          · rcases h1bigk with h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              rcases p231_3 (m.d 0 1) (by simp) with h234 | h234
              · rcases p231_3 (m.d 1 2) (by simp) with h235 | h235
                · linarith only [h0, h235, hlam]
                · linarith only [h235, h4, hlam]
              · linarith only [h234, hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              rcases p231_3 (m.d 0 1) (by simp) with h239 | h239
              · rcases p231_3 (m.d 1 2) (by simp) with h240 | h240
                · linarith only [h0, h240, hlam]
                · linarith only [h240, h5, hlam]
              · linarith only [h239, hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h0, hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h3, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h6, hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h1, hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h4, hlam, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h192, hlam, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h227, hlam, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h2, hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h5, hlam, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h229, h4, hc23, hc45, hlam, hphi, ht34, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h229, hlam, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h3, hlam, p231_0]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p231_1]
            · have p231_0 := h231c.1
              have p231_1 := h231c.2.1
              have p231_2 := h231c.2.2.1
              have p231_3 := h231c.2.2.2
              linarith only [hlam, p231_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
    · rcases m.htr 1 3 4 (by decide) (by decide) with h266 | h266
      · linarith only [h266, h4, h5, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h268 | h268
        · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
          · rcases h1bigk with h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h268, h4, hc01, hlam, hphi, ht0b, ht5b, p270_1, u5ehi3]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h268, hc01, hlam, hphi, ht0b, ht5b, p270_1, u5ehi3]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h268, h4, h5, hc01, hlam, hphi, ht0b, ht5b, p270_1, u5ehi3]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p270_1, u5ehi1]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h0, hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h268, hc12, hlam, hphi, ht01, ht0b, ht5b, p270_1, u5ehi3]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h5, hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p270_1, u5ehi1]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h1, hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h4, hlam, p270_1]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h266, hlam, p270_1]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h265, hc13, hlam, hphi, ht01, ht0b, ht5b, p270_1, u5ehi2]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h2, hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p270_1]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h2, h265, hc01, hlam, hphi, ht0b, ht5b, p270_1, u5ehi2]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h3, hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h265, hlam, p270_1]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h268, hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [h269, hlam, p270_0]
            · have p270_0 := h270c.1
              have p270_1 := h270c.2.1
              have p270_2 := h270c.2.2.1
              have p270_3 := h270c.2.2.2
              linarith only [hlam, p270_0]
          · linarith only [h265, h269, h5, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h297 | h297
          · rcases h1bigk with h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h265, hc01, hlam, hphi, ht0b, ht5b, p298_1, u5ehi1]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              rcases p298_3 (m.d 0 1) (by simp) with h301 | h301
              · rcases p298_3 (m.d 1 2) (by simp) with h302 | h302
                · linarith only [h0, h302, hlam]
                · linarith only [h302, h4, hlam]
              · linarith only [h301, hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h265, h5, hc01, hlam, hphi, ht0b, ht5b, p298_1, u5ehi2]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h265, hc01, hlam, hphi, ht0b, ht5b, p298_1, u5ehi2]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h0, hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p298_1]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h5, hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h265, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p298_1, u5ehi2]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h1, hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h4, hlam, p298_1]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h266, hlam, p298_1]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h268, hlam, p298_1]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h2, hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p298_1]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p298_1]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h2, h265, hc01, hlam, hphi, ht0b, ht5b, p298_1, u5ehi2]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h3, hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h265, hlam, p298_1]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p298_1]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [h297, hlam, p298_0]
            · have p298_0 := h298c.1
              have p298_1 := h298c.2.1
              have p298_2 := h298c.2.2.1
              have p298_3 := h298c.2.2.2
              linarith only [hlam, p298_0]
          · linarith only [h265, h297, h5, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
      · linarith only [h329, h4, h5, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h331 | h331
        · linarith only [h265, h331, h4, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
          · rcases h1bigk with h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              rcases p334_3 (m.d 0 1) (by simp) with h337 | h337
              · rcases p334_3 (m.d 1 2) (by simp) with h338 | h338
                · linarith only [h0, h338, hlam]
                · linarith only [h338, h4, hlam]
              · linarith only [h337, hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h265, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h0, hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h265, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h5, hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h265, hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h1, hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h4, hlam, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h329, hlam, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h331, hlam, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h2, hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h329, hc12, hc34, hlam, hphi, ht23, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h2, h265, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h3, hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p334_1]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [h333, hlam, p334_0]
            · have p334_0 := h334c.1
              have p334_1 := h334c.2.1
              have p334_2 := h334c.2.2.1
              have p334_3 := h334c.2.2.2
              linarith only [hlam, p334_0]
          · rcases h1bigk with h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              rcases p364_3 (m.d 0 1) (by simp) with h367 | h367
              · rcases p364_3 (m.d 1 2) (by simp) with h368 | h368
                · linarith only [h0, h368, hlam]
                · linarith only [h368, h4, hlam]
              · linarith only [h367, hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p364_1, u5ehi1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h0, hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h5, hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h265, hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h1, hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h4, hlam, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h329, hlam, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h331, hlam, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h2, hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h333, hlam, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h3, hlam, p364_0]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p364_1]
            · have p364_0 := h364c.1
              have p364_1 := h364c.2.1
              have p364_2 := h364c.2.2.1
              have p364_3 := h364c.2.2.2
              linarith only [hlam, p364_0]

end R2N4
