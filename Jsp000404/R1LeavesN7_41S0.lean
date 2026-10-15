import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h3 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
  · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
    · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
      · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
        · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
          · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
            · rcases h5bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hlam, p10_0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h0, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h0, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
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
                linarith only [h7, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo4]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h0, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h1, hlam, p10_1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h3, hlam, p10_1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hlam, p10_0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h1, h9, hc02, hc45, hlam, hphi, ht0b, ht5b, p10_1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h0, h3, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo2]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h4, hlam, p10_1]
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
                linarith only [h3, h7, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo4]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h2, hlam, p10_1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h5, hlam, p10_1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h8, hlam, p10_1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h9, hlam, p10_1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hlam, p10_0]
            · rcases h5bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [hlam, p36_0]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p36_1, u1elo0]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p36_1, u1elo0]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h0, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36_1, u1elo0]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h0, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36_1, u1elo0]
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
                linarith only [h8, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36_1, u1elo4]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h0, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36_1, u1elo0]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h0, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36_1, u1elo0]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h1, hlam, p36_1]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h3, hlam, p36_1]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [hlam, p36_0]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h1, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p36_1]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h0, h3, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36_1, u1elo0]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h2, h9, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p36_1]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h4, hlam, p36_1]
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
                linarith only [h9, hlam, p36_0]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h2, hlam, p36_1]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h5, hlam, p36_1]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h8, hlam, p36_1]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [h3, h8, hc35, hlam, hphi, ht01, ht0b, ht5b, p36_1, u1elo4]
              · have p36_0 := h36c.1
                have p36_1 := h36c.2.1
                have p36_2 := h36c.2.2.1
                have p36_3 := h36c.2.2.2
                linarith only [hlam, p36_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
            · linarith only [h6, h62, h8, hlam]
            · rcases h5bigk with h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [hlam, p64_0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p64_1, u1elo0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p64_1, u1elo0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h0, h62, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p64_1, u1elo0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p64_1, u1elo0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h0, hlam, p64_0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [hlam, p64_0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h0, h62, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p64_1, u1elo0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h0, h62, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p64_1, u1elo0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p64_1, u1elo0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h1, hlam, p64_1]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h3, hlam, p64_1]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [hlam, p64_0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h1, h62, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p64_1]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h8, hlam, p64_0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht5b, p64_1, u1elo2]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h4, hlam, p64_1]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h7, hlam, p64_0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [hlam, p64_0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h62, hlam, p64_0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h2, hlam, p64_1]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h5, hlam, p64_1]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p64_1, u1elo4]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [h0, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p64_1, u1elo0]
              · have p64_0 := h64c.1
                have p64_1 := h64c.2.1
                have p64_2 := h64c.2.2.1
                have p64_3 := h64c.2.2.2
                linarith only [hlam, p64_0]
        · linarith only [h0, h4, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
        · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
          · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
            · rcases h5bigk with h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hlam, p94_0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p94_1, u1elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p94_1, u1elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p94_1, u1elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p94_1, u1elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h0, hlam, p94_0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hlam, p94_0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p94_1, u1elo4]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h0, h93, hc45, hlam, hphi, ht01, ht0b, ht5b, p94_1, u1elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p94_1, u1elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h1, hlam, p94_1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h3, hlam, p94_1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hlam, p94_0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h1, h93, hc02, hc45, hlam, hphi, ht0b, ht5b, p94_1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h0, h3, hc45, hlam, hphi, ht01, ht0b, ht5b, p94_1, u1elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht5b, p94_1, u1elo2]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h4, hlam, p94_1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h91, hlam, p94_0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hlam, p94_0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h3, h91, hc45, hlam, hphi, ht01, ht0b, ht5b, p94_1, u1elo4]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h2, hlam, p94_1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h5, hlam, p94_1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h92, hlam, p94_1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h93, hlam, p94_1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hlam, p94_0]
            · linarith only [h2, h6, h91, h93, hc04, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h5, h6, h91, h92, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h122 | h122
          · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
            · rcases h5bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [hlam, p124_0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h0, h91, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p124_1, u1elo0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h0, hlam, p124_0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [hlam, p124_0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h91, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p124_1, u1elo4]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h0, h91, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p124_1, u1elo0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h1, hlam, p124_1]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h3, hlam, p124_1]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [hlam, p124_0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h91, hlam, p124_1]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht0b, ht5b, p124_1]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h0, h3, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo2]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h4, hlam, p124_1]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo4]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [hlam, p124_0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h0, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p124_1, u1elo0]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h2, hlam, p124_1]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h5, hlam, p124_1]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h122, hlam, p124_1]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [h123, hlam, p124_1]
              · have p124_0 := h124c.1
                have p124_1 := h124c.2.1
                have p124_2 := h124c.2.2.1
                have p124_3 := h124c.2.2.2
                linarith only [hlam, p124_0]
            · linarith only [h123, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
            · rcases h5bigk with h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [hlam, p152_0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p152_1, u1elo0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h0, h122, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p152_1, u1elo0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h0, h122, h151, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p152_1, u1elo0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h0, h122, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p152_1, u1elo0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h0, hlam, p152_0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [hlam, p152_0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h122, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p152_1, u1elo4]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h0, h122, h151, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p152_1, u1elo0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h0, h122, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p152_1, u1elo0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h1, hlam, p152_1]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h3, hlam, p152_1]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [hlam, p152_0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h91, hlam, p152_1]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h122, hlam, p152_0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h1, h122, h6, hc23, hc35, hlam, hphi, p152_1]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h4, hlam, p152_1]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h122, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p152_1, u1elo4]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [hlam, p152_0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h0, h122, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p152_1, u1elo0]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h2, hlam, p152_1]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h5, hlam, p152_1]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h122, h6, hc23, hc45, hlam, hphi, ht34, p152_1]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [h151, hlam, p152_1]
              · have p152_0 := h152c.1
                have p152_1 := h152c.2.1
                have p152_2 := h152c.2.2.1
                have p152_3 := h152c.2.2.2
                linarith only [hlam, p152_0]
            · linarith only [h0, h151, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
      · rcases m.htr 2 3 5 (by decide) (by decide) with h180 | h180
        · rcases m.htr 2 4 5 (by decide) (by decide) with h181 | h181
          · linarith only [h181, h3, h5, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h183 | h183
            · linarith only [h179, h181, h183, hlam]
            · rcases h5bigk with h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [hlam, p185_0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p185_1, u1elo0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h0, h180, hc35, hlam, hphi, ht01, ht0b, ht5b, p185_1, u1elo0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h0, h183, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p185_1, u1elo0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h0, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p185_1, u1elo0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h0, hlam, p185_0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [hlam, p185_0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h179, h181, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p185_1, u1elo4]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h0, h183, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p185_1, u1elo0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h5, hlam, p185_0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h1, hlam, p185_1]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h3, hlam, p185_1]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [hlam, p185_0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h1, h183, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p185_1]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h181, hlam, p185_0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht5b, p185_1, u1elo2]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h4, hlam, p185_1]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h180, hlam, p185_0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [hlam, p185_0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h183, hlam, p185_0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h2, hlam, p185_1]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h0, h2, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, p185_1, u1elo0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h0, h180, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, p185_1, u1elo0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, p185_1, u1elo0]
              · have p185_0 := h185c.1
                have p185_1 := h185c.2.1
                have p185_2 := h185c.2.2.1
                have p185_3 := h185c.2.2.2
                linarith only [hlam, p185_0]
        · linarith only [h179, h180, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
        · rcases m.htr 2 4 5 (by decide) (by decide) with h213 | h213
          · linarith only [h213, h3, h5, hlam]
          · linarith only [h179, h212, h213, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h216 | h216
          · linarith only [h212, h216, h4, h5, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h218 | h218
            · linarith only [h218, h4, h5, hlam]
            · rcases h5bigk with h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [hlam, p220_0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p220_1, u1elo0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p220_1, u1elo0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h0, h179, h218, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p220_1, u1elo0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h0, h179, h218, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p220_1, u1elo0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h0, hlam, p220_0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [hlam, p220_0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h179, h216, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p220_1, u1elo4]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h0, h179, h218, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p220_1, u1elo0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h5, hlam, p220_0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h1, hlam, p220_1]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h3, hlam, p220_1]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [hlam, p220_0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h212, hlam, p220_1]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h216, hlam, p220_0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h1, h179, h216, hc23, hc35, hlam, hphi, p220_1]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h4, hlam, p220_1]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h179, h216, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p220_1, u1elo4]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [hlam, p220_0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h218, hlam, p220_0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h2, hlam, p220_1]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h0, h2, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, p220_1, u1elo0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h0, h179, h2, h216, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p220_1, u1elo0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [h0, h2, h212, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p220_1, u1elo0]
              · have p220_0 := h220c.1
                have p220_1 := h220c.2.1
                have p220_2 := h220c.2.2.1
                have p220_3 := h220c.2.2.2
                linarith only [hlam, p220_0]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
    · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
      · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
        · linarith only [h248, h3, h4, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
          · linarith only [h247, h248, h250, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
            · linarith only [h247, h248, h250, h252, hlam]
            · linarith only [h246, h247, h248, h252, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h255 | h255
        · linarith only [h247, h255, h4, hc13, hc34, hlam, hphi]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h257 | h257
          · rcases m.htr 3 4 5 (by decide) (by decide) with h258 | h258
            · rcases h5bigk with h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [hlam, p259_0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p259_1, u1elo0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h0, h255, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p259_1, u1elo0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h0, h255, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p259_1, u1elo0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p259_1, u1elo0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h0, hlam, p259_0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [hlam, p259_0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h255, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p259_1, u1elo4]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h4, hlam, p259_0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p259_1, u1elo0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h1, hlam, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h3, hlam, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [hlam, p259_0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h255, hlam, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht0b, ht5b, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h0, h4, hc13, hc35, hlam, hphi, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h4, hc13, hc35, hlam, hphi, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h255, hc23, hc35, hlam, hphi, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [hlam, p259_0]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                rcases p259_3 (m.d 0 5) (by simp) with h279 | h279
                · linarith only [h0, h279, hc45, hlam, hphi, ht01, ht0b, ht5b, p259_1, u1elo0]
                · linarith only [h2, h279, hlam]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h2, hlam, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h246, hlam, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h257, hlam, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [h258, hlam, p259_1]
              · have p259_0 := h259c.1
                have p259_1 := h259c.2.1
                have p259_2 := h259c.2.2.1
                have p259_3 := h259c.2.2.2
                linarith only [hlam, p259_0]
            · linarith only [h0, h246, h247, h258, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h288 | h288
            · rcases h5bigk with h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [hlam, p289_0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p289_1, u1elo0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h0, h247, h257, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p289_1, u1elo0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p289_1, u1elo0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h0, h247, h257, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p289_1, u1elo0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h0, hlam, p289_0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [hlam, p289_0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h247, h257, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p289_1, u1elo4]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h4, hlam, p289_0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h0, h247, h257, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p289_1, u1elo0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h1, hlam, p289_1]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h3, hlam, p289_1]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [hlam, p289_0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h255, hlam, p289_1]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h257, hlam, p289_0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h1, h247, h257, hc23, hc35, hlam, hphi, p289_1]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h247, h257, h3, hc23, hc35, hlam, hphi, p289_1]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h247, h257, hc23, hc35, hlam, hphi, p289_1]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [hlam, p289_0]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h247, h257, h288, hc23, hc34, hlam, hphi, p289_1]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h2, hlam, p289_1]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h246, hlam, p289_1]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h246, h247, h257, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p289_1, u1elo4]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [h288, hlam, p289_1]
              · have p289_0 := h289c.1
                have p289_1 := h289c.2.1
                have p289_2 := h289c.2.2.1
                have p289_3 := h289c.2.2.2
                linarith only [hlam, p289_0]
            · linarith only [h0, h246, h247, h288, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h316 | h316
      · rcases m.htr 2 3 5 (by decide) (by decide) with h317 | h317
        · linarith only [h3, h317, h4, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h319 | h319
          · linarith only [h246, h3, h316, h317, h319, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h321 | h321
            · linarith only [h246, h3, h316, h317, h321, hlam]
            · rcases h5bigk with h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p323_1, u1elo0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p323_1, u1elo0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, h316, h317, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p323_1, u1elo0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, h316, h317, h321, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p323_1, u1elo0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h316, h317, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p323_1, u1elo4]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h4, hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h246, hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h1, hlam, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h3, hlam, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h317, hlam, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h319, hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h1, h316, h317, h321, hc34, hc45, hlam, hphi, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, h2, h3, h316, h317, h321, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p323_1, u1elo0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, h2, h316, h317, h321, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p323_1, u1elo0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h321, hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h2, hlam, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, h2, h3, h316, h317, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p323_1, u1elo0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, h2, h316, h317, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p323_1, u1elo0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, p323_1, u1elo0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [hlam, p323_0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h349 | h349
        · linarith only [h316, h349, h4, hc13, hc34, hlam, hphi]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h351 | h351
          · linarith only [h246, h3, h351, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h353 | h353
            · rcases h5bigk with h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [hlam, p354_0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p354_1, u1elo0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p354_1, u1elo0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h0, h316, h351, h353, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p354_1, u1elo0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h0, h316, h351, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p354_1, u1elo0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h0, hlam, p354_0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [hlam, p354_0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h316, h351, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p354_1, u1elo4]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h4, hlam, p354_0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h246, hlam, p354_0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h1, hlam, p354_1]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h3, hlam, p354_1]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [hlam, p354_0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h349, hlam, p354_1]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h351, hlam, p354_0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h1, h316, h351, hc23, hc35, hlam, hphi, p354_1]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h3, h316, h351, hc23, hc35, hlam, hphi, p354_1]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h316, h351, hc23, hc35, hlam, hphi, p354_1]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [hlam, p354_0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h316, h351, h353, hc23, hc34, hlam, hphi, p354_1]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h2, hlam, p354_1]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h3, h316, h351, hc23, hc45, hlam, hphi, ht34, p354_1]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h0, h2, h316, h351, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p354_1, u1elo0]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [h353, hlam, p354_1]
              · have p354_0 := h354c.1
                have p354_1 := h354c.2.1
                have p354_2 := h354c.2.2.1
                have p354_3 := h354c.2.2.2
                linarith only [hlam, p354_0]
            · rcases h5bigk with h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [hlam, p380_0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h0, h3, h316, h351, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p380_1, u1elo0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h0, h316, h351, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p380_1, u1elo0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p380_1, u1elo0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h0, h353, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p380_1, u1elo0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h0, hlam, p380_0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [hlam, p380_0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h316, h351, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p380_1, u1elo4]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h4, hlam, p380_0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h246, hlam, p380_0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h1, hlam, p380_1]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h3, hlam, p380_1]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [hlam, p380_0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h349, hlam, p380_1]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h351, hlam, p380_0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h1, h316, h351, hc23, hc35, hlam, hphi, p380_1]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h3, h316, h351, hc23, hc35, hlam, hphi, p380_1]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h316, h351, hc23, hc35, hlam, hphi, p380_1]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [hlam, p380_0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h353, hlam, p380_0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h2, hlam, p380_1]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h3, h316, h351, hc23, hc45, hlam, hphi, ht34, p380_1]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h0, h2, h316, h351, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p380_1, u1elo0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, p380_1, u1elo0]
              · have p380_0 := h380c.1
                have p380_1 := h380c.2.1
                have p380_2 := h380c.2.2.1
                have p380_3 := h380c.2.2.2
                linarith only [hlam, p380_0]

end R2N4
