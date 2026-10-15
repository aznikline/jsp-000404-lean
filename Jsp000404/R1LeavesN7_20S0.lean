import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
          · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
            · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                · linarith only [h0, h12, h15, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h12, h14, h15, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h10, h14, h18, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h2bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, h13, hc01, hc35, hlam, hphi, ht0b, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    rcases p20_3 (m.d 0 2) (by simp) with h24 | h24
                    · rcases p20_3 (m.d 1 2) (by simp) with h25 | h25
                      · linarith only [h0, h25, hlam]
                      · linarith only [h25, h8, hlam]
                    · linarith only [h24, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    rcases p20_3 (m.d 0 2) (by simp) with h29 | h29
                    · rcases p20_3 (m.d 1 2) (by simp) with h30 | h30
                      · linarith only [h0, h30, hlam]
                      · linarith only [h30, h9, hlam]
                    · linarith only [h29, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h13, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, h12, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h2, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h7, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, h12, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h3, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h8, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h12, hlam, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h14, hlam, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h4, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h9, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h13, hlam, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, h12, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [hlam, p20_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
              · linarith only [h12, h13, h54, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                · linarith only [h0, h10, h54, h56, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h10, h11, h12, h13, h56, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
            · linarith only [h0, h10, h12, h59, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
              · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                · rcases h2bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h0, h10, h59, h62, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    rcases p63_3 (m.d 0 2) (by simp) with h66 | h66
                    · rcases p63_3 (m.d 1 2) (by simp) with h67 | h67
                      · linarith only [h0, h67, hlam]
                      · linarith only [h67, h7, hlam]
                    · linarith only [h66, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h0, h61, hc01, hc45, hlam, hphi, ht0b, ht5b, p63_1]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    rcases p63_3 (m.d 0 2) (by simp) with h72 | h72
                    · rcases p63_3 (m.d 1 2) (by simp) with h73 | h73
                      · linarith only [h0, h73, hlam]
                      · linarith only [h73, h9, hlam]
                    · linarith only [h72, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h0, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h0, h61, hc01, hc45, hlam, hphi, ht0b, ht5b, p63_1]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p63_1]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h2, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h7, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h12, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h59, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h3, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h8, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h10, h12, h59, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p63_1]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h4, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h9, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [h61, hlam, p63_0]
                  · have p63_0 := h63c.1
                    have p63_1 := h63c.2.1
                    have p63_2 := h63c.2.2.1
                    have p63_3 := h63c.2.2.2
                    linarith only [hlam, p63_0]
                · linarith only [h0, h10, h11, h12, h62, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                · linarith only [h0, h10, h61, h7, h98, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h10, h11, h12, h7, h98, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
          · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
            · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
              · linarith only [h0, h103, h11, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                · linarith only [h0, h101, h105, h11, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h2bigk with h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h0, h102, h105, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    rcases p107_3 (m.d 0 2) (by simp) with h111 | h111
                    · rcases p107_3 (m.d 1 2) (by simp) with h112 | h112
                      · linarith only [h0, h112, hlam]
                      · linarith only [h112, h8, hlam]
                    · linarith only [h111, hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    rcases p107_3 (m.d 0 2) (by simp) with h116 | h116
                    · rcases p107_3 (m.d 1 2) (by simp) with h117 | h117
                      · linarith only [h0, h117, hlam]
                      · linarith only [h117, h9, hlam]
                    · linarith only [h116, hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h0, hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h102, h105, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h2, hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h7, hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h0, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h0, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h3, hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h8, hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h101, hlam, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h103, hlam, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h4, hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h9, hlam, p107_0]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h102, hlam, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [h0, h101, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                  · have p107_0 := h107c.1
                    have p107_1 := h107c.2.1
                    have p107_2 := h107c.2.2.1
                    have p107_3 := h107c.2.2.2
                    linarith only [hlam, p107_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
              · linarith only [h0, h11, h141, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                · linarith only [h101, h11, h143, h8, hlam]
                · rcases h2bigk with h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h0, h101, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h0, h101, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    rcases p145_3 (m.d 0 2) (by simp) with h149 | h149
                    · rcases p145_3 (m.d 1 2) (by simp) with h150 | h150
                      · linarith only [h0, h150, hlam]
                      · linarith only [h150, h8, hlam]
                    · linarith only [h149, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h0, h101, h102, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h0, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h101, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h0, h101, h102, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h2, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h7, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h102, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h102, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h3, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h8, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h101, hlam, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h141, hlam, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h4, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h9, hlam, p145_0]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [h0, h101, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p145_1]
                  · have p145_0 := h145c.1
                    have p145_1 := h145c.2.1
                    have p145_2 := h145c.2.2.1
                    have p145_3 := h145c.2.2.2
                    linarith only [hlam, p145_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
            · linarith only [h0, h10, h101, h175, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h177 | h177
              · linarith only [h0, h10, h101, h11, h177, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h179 | h179
                · linarith only [h10, h11, h179, hlam]
                · rcases h2bigk with h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h0, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p181_1]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    rcases p181_3 (m.d 0 2) (by simp) with h184 | h184
                    · rcases p181_3 (m.d 1 2) (by simp) with h185 | h185
                      · linarith only [h0, h185, hlam]
                      · linarith only [h185, h7, hlam]
                    · linarith only [h184, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    rcases p181_3 (m.d 0 2) (by simp) with h189 | h189
                    · rcases p181_3 (m.d 1 2) (by simp) with h190 | h190
                      · linarith only [h0, h190, hlam]
                      · linarith only [h190, h8, hlam]
                    · linarith only [h189, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    rcases p181_3 (m.d 0 2) (by simp) with h194 | h194
                    · rcases p181_3 (m.d 1 2) (by simp) with h195 | h195
                      · linarith only [h0, h195, hlam]
                      · linarith only [h195, h9, hlam]
                    · linarith only [h194, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h0, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h0, h101, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h0, h101, h177, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h2, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h7, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h101, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h175, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h3, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h8, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h177, hlam, p181_1]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h4, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h9, hlam, p181_0]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [h0, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p181_1]
                  · have p181_0 := h181c.1
                    have p181_1 := h181c.2.1
                    have p181_2 := h181c.2.2.1
                    have p181_3 := h181c.2.2.2
                    linarith only [hlam, p181_0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
        · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
          · linarith only [h10, h220, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h222 | h222
            · rcases m.htr 2 4 5 (by decide) (by decide) with h223 | h223
              · rcases m.htr 3 4 5 (by decide) (by decide) with h224 | h224
                · rcases h2bigk with h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h0, h222, h224, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p225_1]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h0, h222, h224, hc01, hc45, hlam, hphi, ht0b, ht5b, p225_1]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h0, h220, h222, h224, hc01, hc45, hlam, hphi, ht0b, ht5b, p225_1]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    rcases p225_3 (m.d 0 2) (by simp) with h230 | h230
                    · rcases p225_3 (m.d 1 2) (by simp) with h231 | h231
                      · linarith only [h0, h231, hlam]
                      · linarith only [h231, h9, hlam]
                    · linarith only [h230, hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h0, hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h222, h224, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p225_1]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h0, h220, h222, h224, hc01, hc45, hlam, hphi, ht0b, ht5b, p225_1]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p225_1]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h2, hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h7, hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h220, hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h10, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p225_1]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h3, hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h8, hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p225_1]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h1, h222, h224, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p225_1]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h4, hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h9, hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h222, hlam, p225_1]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [h223, hlam, p225_0]
                  · have p225_0 := h225c.1
                    have p225_1 := h225c.2.1
                    have p225_2 := h225c.2.2.1
                    have p225_3 := h225c.2.2.2
                    linarith only [hlam, p225_0]
                · linarith only [h0, h10, h2, h222, h224, h5, h6, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h10, h2, h219, h220, h222, h223, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h257 | h257
              · rcases m.htr 3 4 5 (by decide) (by decide) with h258 | h258
                · rcases h2bigk with h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    rcases p259_3 (m.d 0 2) (by simp) with h262 | h262
                    · rcases p259_3 (m.d 1 2) (by simp) with h263 | h263
                      · linarith only [h0, h263, hlam]
                      · linarith only [h263, h7, hlam]
                    · linarith only [h262, hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h0, h257, hc01, hc45, hlam, hphi, ht0b, ht5b, p259_1]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    rcases p259_3 (m.d 0 2) (by simp) with h268 | h268
                    · rcases p259_3 (m.d 1 2) (by simp) with h269 | h269
                      · linarith only [h0, h269, hlam]
                      · linarith only [h269, h9, hlam]
                    · linarith only [h268, hlam, p259_0]
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
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h0, h257, hc01, hc45, hlam, hphi, ht0b, ht5b, p259_1]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h0, h222, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h2, hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h7, hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h220, hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h222, hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h3, hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h8, hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h0, h222, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h4, hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h9, hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [h257, hlam, p259_0]
                  · have p259_0 := h259c.1
                    have p259_1 := h259c.2.1
                    have p259_2 := h259c.2.2.1
                    have p259_3 := h259c.2.2.2
                    linarith only [hlam, p259_0]
                · linarith only [h10, h219, h258, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h294 | h294
                · rcases h2bigk with h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    rcases p295_3 (m.d 0 2) (by simp) with h298 | h298
                    · rcases p295_3 (m.d 1 2) (by simp) with h299 | h299
                      · linarith only [h0, h299, hlam]
                      · linarith only [h299, h7, hlam]
                    · linarith only [h298, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    rcases p295_3 (m.d 0 2) (by simp) with h303 | h303
                    · rcases p295_3 (m.d 1 2) (by simp) with h304 | h304
                      · linarith only [h0, h304, hlam]
                      · linarith only [h304, h8, hlam]
                    · linarith only [h303, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    rcases p295_3 (m.d 0 2) (by simp) with h308 | h308
                    · rcases p295_3 (m.d 1 2) (by simp) with h309 | h309
                      · linarith only [h0, h309, hlam]
                      · linarith only [h309, h9, hlam]
                    · linarith only [h308, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h0, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h0, h220, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p295_1]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h2, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h7, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h220, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h222, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h3, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h8, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h219, h257, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p295_1]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h257, hlam, p295_1]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h4, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h9, hlam, p295_0]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [h0, h10, h2, h219, h257, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p295_1]
                  · have p295_0 := h295c.1
                    have p295_1 := h295c.2.1
                    have p295_2 := h295c.2.2.1
                    have p295_3 := h295c.2.2.2
                    linarith only [hlam, p295_0]
                · linarith only [h10, h219, h294, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
          · linarith only [h10, h334, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
            · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
              · linarith only [h0, h10, h219, h3, h336, h337, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h334, h336, h337, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h340 | h340
              · linarith only [h0, h10, h219, h340, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h342 | h342
                · rcases h2bigk with h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    rcases p343_3 (m.d 0 2) (by simp) with h346 | h346
                    · rcases p343_3 (m.d 1 2) (by simp) with h347 | h347
                      · linarith only [h0, h347, hlam]
                      · linarith only [h347, h7, hlam]
                    · linarith only [h346, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    rcases p343_3 (m.d 0 2) (by simp) with h351 | h351
                    · rcases p343_3 (m.d 1 2) (by simp) with h352 | h352
                      · linarith only [h0, h352, hlam]
                      · linarith only [h352, h8, hlam]
                    · linarith only [h351, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    rcases p343_3 (m.d 0 2) (by simp) with h356 | h356
                    · rcases p343_3 (m.d 1 2) (by simp) with h357 | h357
                      · linarith only [h0, h357, hlam]
                      · linarith only [h357, h9, hlam]
                    · linarith only [h356, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h0, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p343_1]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h0, h340, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p343_1]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h2, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h7, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h334, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h336, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h3, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h8, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h340, hlam, p343_1]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h4, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h9, hlam, p343_0]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h219, h9, hc23, hc45, hlam, hphi, ht34, p343_1]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [h0, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p343_1]
                  · have p343_0 := h343c.1
                    have p343_1 := h343c.2.1
                    have p343_2 := h343c.2.2.1
                    have p343_3 := h343c.2.2.2
                    linarith only [hlam, p343_0]
                · rcases h2bigk with h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    rcases p381_3 (m.d 0 2) (by simp) with h384 | h384
                    · rcases p381_3 (m.d 1 2) (by simp) with h385 | h385
                      · linarith only [h0, h385, hlam]
                      · linarith only [h385, h7, hlam]
                    · linarith only [h384, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    rcases p381_3 (m.d 0 2) (by simp) with h389 | h389
                    · rcases p381_3 (m.d 1 2) (by simp) with h390 | h390
                      · linarith only [h0, h390, hlam]
                      · linarith only [h390, h8, hlam]
                    · linarith only [h389, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    rcases p381_3 (m.d 0 2) (by simp) with h394 | h394
                    · rcases p381_3 (m.d 1 2) (by simp) with h395 | h395
                      · linarith only [h0, h395, hlam]
                      · linarith only [h395, h9, hlam]
                    · linarith only [h394, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, h334, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, h334, h340, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h2, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h7, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h334, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h336, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h3, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h8, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h340, hlam, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h4, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h9, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hlam, p381_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h419 | h419
      · rcases m.htr 1 4 5 (by decide) (by decide) with h420 | h420
        · linarith only [h419, h420, h7, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h422 | h422
          · linarith only [h0, h4, h422, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h4, h419, h422, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h425 | h425
        · linarith only [h425, h8, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h427 | h427
          · linarith only [h0, h4, h419, h427, h7, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h429 | h429
            · linarith only [h0, h4, h427, h429, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h431 | h431
              · linarith only [h425, h431, h8, h9, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                · linarith only [h427, h431, h433, h8, h9, hc23, hc34, hlam, hphi]
                · rcases h2bigk with h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, h427, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    rcases p435_3 (m.d 0 2) (by simp) with h438 | h438
                    · rcases p435_3 (m.d 1 2) (by simp) with h439 | h439
                      · linarith only [h0, h439, hlam]
                      · linarith only [h439, h7, hlam]
                    · linarith only [h438, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    rcases p435_3 (m.d 0 2) (by simp) with h443 | h443
                    · rcases p435_3 (m.d 1 2) (by simp) with h444 | h444
                      · linarith only [h0, h444, hlam]
                      · linarith only [h444, h8, hlam]
                    · linarith only [h443, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, h427, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, h427, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h9, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h2, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h7, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h427, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h429, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h3, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h8, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h431, hlam, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h4, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, h2, h429, h433, h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, h2, h427, h429, h433, h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hlam, p435_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h469 | h469
    · rcases m.htr 1 3 4 (by decide) (by decide) with h470 | h470
      · linarith only [h470, h7, h8, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h472 | h472
        · rcases m.htr 2 3 4 (by decide) (by decide) with h473 | h473
          · linarith only [h470, h473, h7, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h475 | h475
            · linarith only [h0, h2, h473, h475, h5, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h477 | h477
              · rcases m.htr 3 4 5 (by decide) (by decide) with h478 | h478
                · rcases h2bigk with h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h0, h469, h475, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p479_1]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    rcases p479_3 (m.d 0 2) (by simp) with h482 | h482
                    · rcases p479_3 (m.d 1 2) (by simp) with h483 | h483
                      · linarith only [h0, h483, hlam]
                      · linarith only [h483, h7, hlam]
                    · linarith only [h482, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h0, h469, h475, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p479_1]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    rcases p479_3 (m.d 0 2) (by simp) with h488 | h488
                    · rcases p479_3 (m.d 1 2) (by simp) with h489 | h489
                      · linarith only [h0, h489, hlam]
                      · linarith only [h469, h489, hlam]
                    · linarith only [h488, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h0, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h8, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p479_1]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h8, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h0, h3, h475, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p479_1]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h2, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h7, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h473, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h475, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h3, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p479_1]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h0, h2, h473, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p479_1]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h0, h2, h473, h475, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p479_1]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h4, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h469, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h469, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p479_1]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [h477, hlam, p479_0]
                  · have p479_0 := h479c.1
                    have p479_1 := h479c.2.1
                    have p479_2 := h479c.2.2.1
                    have p479_3 := h479c.2.2.2
                    linarith only [hlam, p479_0]
                · linarith only [h469, h473, h477, h478, h8, hlam]
              · linarith only [h0, h2, h469, h477, h5, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h469, h472, h8, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
      · linarith only [h516, h7, h8, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h518 | h518
        · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
          · linarith only [h516, h519, h7, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h521 | h521
            · linarith only [h0, h2, h5, h519, h521, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h523 | h523
              · rcases m.htr 3 4 5 (by decide) (by decide) with h524 | h524
                · rcases h2bigk with h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p525_1]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    rcases p525_3 (m.d 0 2) (by simp) with h528 | h528
                    · rcases p525_3 (m.d 1 2) (by simp) with h529 | h529
                      · linarith only [h0, h529, hlam]
                      · linarith only [h529, h7, hlam]
                    · linarith only [h528, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h0, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p525_1]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h0, h469, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p525_1]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h0, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h8, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p525_1]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h8, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h469, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h2, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h7, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h519, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h521, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h3, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [hc12, hc24, hlam, hphi, p525_1]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h0, h2, h5, h519, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p525_1]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h0, h2, h469, h5, h519, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p525_1]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h4, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h7, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p525_1]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p525_1]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [h523, hlam, p525_0]
                  · have p525_0 := h525c.1
                    have p525_1 := h525c.2.1
                    have p525_2 := h525c.2.2.1
                    have p525_3 := h525c.2.2.2
                    linarith only [hlam, p525_0]
                · linarith only [h0, h2, h5, h519, h524, h6, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h518, h523, h7, h8, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h557 | h557
          · linarith only [h0, h3, h557, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h559 | h559
            · linarith only [h0, h3, h559, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h561 | h561
              · linarith only [h0, h2, h5, h518, h557, h561, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h2, h5, h561, h6, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

end R2N4
