import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
  · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
      · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
        · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
          · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
            · linarith only [h0, h15, h18, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h15, h17, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h12, h17, h21, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h1bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h16, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h12, h14, h15, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h14, h15, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                rcases p23_3 (m.d 0 1) (by simp) with h28 | h28
                · rcases p23_3 (m.d 1 2) (by simp) with h29 | h29
                  · linarith only [h0, h29, hlam]
                  · linarith only [h11, h29, hlam]
                · linarith only [h28, hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h0, hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h12, h14, h15, h17, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h0, h14, h15, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h0, h14, h15, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h1, hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h9, hlam, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h14, h15, h17, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h0, h14, h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h2, hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h10, hlam, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h12, hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h0, h12, h14, h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h3, hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h11, hlam, p23_1]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h13, hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [h14, hlam, p23_0]
              · have p23_0 := h23c.1
                have p23_1 := h23c.2.1
                have p23_2 := h23c.2.2.1
                have p23_3 := h23c.2.2.2
                linarith only [hlam, p23_0]
        · linarith only [h0, h13, h15, h16, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
        · linarith only [h0, h12, h15, h54, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
          · rcases m.htr 3 4 5 (by decide) (by decide) with h57 | h57
            · rcases h1bigk with h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h12, h54, h57, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h12, h54, h57, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                rcases p58_3 (m.d 0 1) (by simp) with h62 | h62
                · rcases p58_3 (m.d 1 2) (by simp) with h63 | h63
                  · linarith only [h0, h63, hlam]
                  · linarith only [h10, h63, hlam]
                · linarith only [h62, hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                rcases p58_3 (m.d 0 1) (by simp) with h67 | h67
                · rcases p58_3 (m.d 1 2) (by simp) with h68 | h68
                  · linarith only [h0, h68, hlam]
                  · linarith only [h11, h68, hlam]
                · linarith only [h67, hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h0, hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h12, h54, h57, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h0, h10, h56, hc01, hc45, hlam, hphi, ht0b, ht5b, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h0, h13, h54, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h1, hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h9, hlam, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h1, h10, h56, hc01, hc45, hlam, hphi, ht0b, ht5b, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h0, h13, h54, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h2, hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h10, hlam, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h12, hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h13, h2, h54, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h3, hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h11, hlam, p58_1]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h13, hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [h14, hlam, p58_0]
              · have p58_0 := h58c.1
                have p58_1 := h58c.2.1
                have p58_2 := h58c.2.2.1
                have p58_3 := h58c.2.2.2
                linarith only [hlam, p58_0]
            · linarith only [h0, h10, h56, h57, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
            · linarith only [h0, h12, h56, h9, h93, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h12, h14, h15, h9, h93, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
      · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
        · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
          · linarith only [h0, h10, h14, h98, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
            · linarith only [h10, h100, h14, h96, hlam]
            · rcases h1bigk with h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h100, h9, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p102_1]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                rcases p102_3 (m.d 0 1) (by simp) with h105 | h105
                · rcases p102_3 (m.d 1 2) (by simp) with h106 | h106
                  · linarith only [h0, h106, hlam]
                  · linarith only [h106, h9, hlam]
                · linarith only [h105, hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                rcases p102_3 (m.d 0 1) (by simp) with h110 | h110
                · rcases p102_3 (m.d 1 2) (by simp) with h111 | h111
                  · linarith only [h0, h111, hlam]
                  · linarith only [h10, h111, hlam]
                · linarith only [h110, hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                rcases p102_3 (m.d 0 1) (by simp) with h115 | h115
                · rcases p102_3 (m.d 1 2) (by simp) with h116 | h116
                  · linarith only [h0, h116, hlam]
                  · linarith only [h11, h116, hlam]
                · linarith only [h115, hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h0, hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h0, h100, h9, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p102_1]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                rcases p102_3 (m.d 0 1) (by simp) with h123 | h123
                · rcases p102_3 (m.d 1 2) (by simp) with h124 | h124
                  · rcases p102_3 (m.d 1 3) (by simp) with h125 | h125
                    · linarith only [h125, h9, hlam]
                    · linarith only [h12, h125, hlam]
                  · linarith only [h10, h124, hlam]
                · linarith only [h123, h2, hlam]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                rcases p102_3 (m.d 0 1) (by simp) with h130 | h130
                · rcases p102_3 (m.d 1 2) (by simp) with h131 | h131
                  · rcases p102_3 (m.d 1 3) (by simp) with h132 | h132
                    · linarith only [h132, h9, hlam]
                    · linarith only [h13, h132, hlam]
                  · linarith only [h11, h131, hlam]
                · linarith only [h130, h3, hlam]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h1, hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h9, hlam, p102_1]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                rcases p102_3 (m.d 0 1) (by simp) with h140 | h140
                · rcases p102_3 (m.d 1 2) (by simp) with h141 | h141
                  · rcases p102_3 (m.d 1 3) (by simp) with h142 | h142
                    · rcases p102_3 (m.d 1 4) (by simp) with h143 | h143
                      · linarith only [h12, h143, hlam]
                      · rcases p102_3 (m.d 1 5) (by simp) with h145 | h145
                        · linarith only [h13, h145, hlam]
                        · linarith only [h14, h145, hlam]
                    · linarith only [h12, h142, hlam]
                  · linarith only [h10, h141, hlam]
                · linarith only [h140, h2, hlam]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                rcases p102_3 (m.d 0 1) (by simp) with h151 | h151
                · rcases p102_3 (m.d 1 2) (by simp) with h152 | h152
                  · rcases p102_3 (m.d 1 3) (by simp) with h153 | h153
                    · rcases p102_3 (m.d 1 4) (by simp) with h154 | h154
                      · linarith only [h12, h154, hlam]
                      · rcases p102_3 (m.d 1 5) (by simp) with h156 | h156
                        · linarith only [h13, h156, hlam]
                        · rcases h3bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h0, h14, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p102_1, p158_1]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h0, h100, h4, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            rcases p158_3 (m.d 0 3) (by simp) with h162 | h162
                            · rcases p158_3 (m.d 1 3) (by simp) with h163 | h163
                              · linarith only [h1, h163, hlam]
                              · linarith only [h12, h163, hlam]
                            · linarith only [h162, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            rcases p158_3 (m.d 0 3) (by simp) with h167 | h167
                            · rcases p158_3 (m.d 1 3) (by simp) with h168 | h168
                              · linarith only [h1, h168, hlam]
                              · linarith only [h13, h168, hlam]
                            · linarith only [h167, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h1, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h100, h97, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p158_1]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h0, h100, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h4, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h9, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h0, h100, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h6, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h12, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h96, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h100, hlam, p158_1]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h7, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h13, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h97, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            linarith only [hlam, p158_0]
                    · linarith only [h13, h153, hlam]
                  · linarith only [h11, h152, hlam]
                · linarith only [h151, h3, hlam]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h2, hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h10, hlam, p102_1]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h12, hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h14, hlam, p102_1]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h3, hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h11, hlam, p102_1]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [h13, hlam, p102_0]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                rcases p102_3 (m.d 0 1) (by simp) with h203 | h203
                · rcases p102_3 (m.d 1 2) (by simp) with h204 | h204
                  · rcases p102_3 (m.d 1 3) (by simp) with h205 | h205
                    · rcases p102_3 (m.d 1 4) (by simp) with h206 | h206
                      · linarith only [h14, h206, hlam]
                      · rcases p102_3 (m.d 1 5) (by simp) with h208 | h208
                        · rcases h3bigk with h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, h4, h9, h97, hc01, hc35, hlam, hphi, ht0b, ht5b, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, h4, h97, hc01, hc35, hlam, hphi, ht0b, ht5b, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            rcases p209_3 (m.d 0 3) (by simp) with h213 | h213
                            · rcases p209_3 (m.d 1 3) (by simp) with h214 | h214
                              · linarith only [h1, h214, hlam]
                              · linarith only [h12, h214, hlam]
                            · linarith only [h213, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            rcases p209_3 (m.d 0 3) (by simp) with h218 | h218
                            · rcases p209_3 (m.d 1 3) (by simp) with h219 | h219
                              · linarith only [h1, h219, hlam]
                              · linarith only [h13, h219, hlam]
                            · linarith only [h218, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h1, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h100, h97, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, h100, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h4, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h9, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, h100, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h6, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h12, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h96, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h100, hlam, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h7, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h13, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h97, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [hlam, p209_0]
                        · linarith only [h14, h208, hlam]
                    · linarith only [h12, h205, hlam]
                  · linarith only [h10, h204, hlam]
                · linarith only [h2, h203, hlam]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [hlam, p102_0]
        · linarith only [h0, h13, h9, h96, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h249 | h249
        · linarith only [h0, h12, h249, h9, h96, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h251 | h251
          · linarith only [h0, h12, h14, h251, h5, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h253 | h253
            · linarith only [h12, h14, h253, hlam]
            · rcases h1bigk with h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h12, h9, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h12, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                rcases p255_3 (m.d 0 1) (by simp) with h259 | h259
                · rcases p255_3 (m.d 1 2) (by simp) with h260 | h260
                  · linarith only [h0, h260, hlam]
                  · linarith only [h10, h260, hlam]
                · linarith only [h259, hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                rcases p255_3 (m.d 0 1) (by simp) with h264 | h264
                · rcases p255_3 (m.d 1 2) (by simp) with h265 | h265
                  · linarith only [h0, h265, hlam]
                  · linarith only [h11, h265, hlam]
                · linarith only [h264, hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h0, hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h13, h253, h96, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h0, h12, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h0, h13, h253, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h1, hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h9, hlam, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h1, h12, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h0, h13, h253, h9, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h2, hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h10, hlam, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h12, hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h14, hlam, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h3, hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h11, hlam, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h13, hlam, p255_0]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [h12, h3, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1]
              · have p255_0 := h255c.1
                have p255_1 := h255c.2.1
                have p255_2 := h255c.2.2.1
                have p255_3 := h255c.2.2.2
                linarith only [hlam, p255_0]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
    · linarith only [h12, h13, h289, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
      · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
        · linarith only [h13, h292, h9, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h294 | h294
          · linarith only [h10, h289, h294, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h296 | h296
            · linarith only [h10, h13, h289, h291, h296, h9, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
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
                linarith only [h291, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p298_1]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                rcases p298_3 (m.d 0 1) (by simp) with h301 | h301
                · rcases p298_3 (m.d 1 2) (by simp) with h302 | h302
                  · linarith only [h0, h302, hlam]
                  · linarith only [h302, h9, hlam]
                · linarith only [h301, hlam, p298_0]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                rcases p298_3 (m.d 0 1) (by simp) with h306 | h306
                · rcases p298_3 (m.d 1 2) (by simp) with h307 | h307
                  · linarith only [h0, h307, hlam]
                  · linarith only [h10, h307, hlam]
                · linarith only [h306, hlam, p298_0]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                rcases p298_3 (m.d 0 1) (by simp) with h311 | h311
                · rcases p298_3 (m.d 1 2) (by simp) with h312 | h312
                  · linarith only [h0, h312, hlam]
                  · linarith only [h11, h312, hlam]
                · linarith only [h311, hlam, p298_0]
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
                linarith only [h0, h291, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p298_1]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                rcases p298_3 (m.d 0 1) (by simp) with h319 | h319
                · rcases p298_3 (m.d 1 2) (by simp) with h320 | h320
                  · rcases p298_3 (m.d 1 3) (by simp) with h321 | h321
                    · linarith only [h321, h9, hlam]
                    · linarith only [h12, h321, hlam]
                  · linarith only [h10, h320, hlam]
                · linarith only [h2, h319, hlam]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h0, h13, h291, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p298_1]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h1, hlam, p298_0]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h9, hlam, p298_1]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [hlam, p298_0]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h0, h10, h13, h291, h296, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p298_1]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h13, hlam, p298_1]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h2, hlam, p298_0]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h10, hlam, p298_1]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h12, hlam, p298_0]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [hlam, p298_0]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h289, hlam, p298_1]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h3, hlam, p298_0]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h11, hlam, p298_1]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [h291, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p298_1]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                rcases p298_3 (m.d 0 1) (by simp) with h340 | h340
                · rcases p298_3 (m.d 1 2) (by simp) with h341 | h341
                  · rcases p298_3 (m.d 1 3) (by simp) with h342 | h342
                    · linarith only [h13, h342, hlam]
                    · linarith only [h12, h342, hlam]
                  · linarith only [h10, h341, hlam]
                · linarith only [h2, h340, hlam]
              · have p298_0 := h298c.1
                have p298_1 := h298c.2.1
                have p298_2 := h298c.2.2.1
                have p298_3 := h298c.2.2.2
                linarith only [hlam, p298_0]
      · linarith only [h12, h13, h291, hc23, hc35, hlam, hphi]

end R2N4
