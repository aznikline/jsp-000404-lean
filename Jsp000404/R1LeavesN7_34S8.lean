import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4bigk := hb4.1
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
                            rcases p158_3 (m.d 0 3) (by simp) with h161 | h161
                            · rcases p158_3 (m.d 1 3) (by simp) with h162 | h162
                              · linarith only [h1, h162, hlam]
                              · linarith only [h162, h9, hlam]
                            · linarith only [h161, h4, hlam]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            rcases p158_3 (m.d 0 3) (by simp) with h166 | h166
                            · rcases p158_3 (m.d 1 3) (by simp) with h167 | h167
                              · linarith only [h1, h167, hlam]
                              · linarith only [h12, h167, hlam]
                            · linarith only [h166, hlam, p158_0]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            rcases p158_3 (m.d 0 3) (by simp) with h171 | h171
                            · rcases p158_3 (m.d 1 3) (by simp) with h172 | h172
                              · linarith only [h1, h172, hlam]
                              · linarith only [h13, h172, hlam]
                            · linarith only [h171, hlam, p158_0]
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
                            linarith only [h1, h100, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            rcases p158_3 (m.d 0 3) (by simp) with h179 | h179
                            · rcases p158_3 (m.d 1 3) (by simp) with h180 | h180
                              · rcases p158_3 (m.d 2 3) (by simp) with h181 | h181
                                · linarith only [h181, h9, hlam]
                                · linarith only [h181, h96, hlam]
                              · linarith only [h180, hlam, p158_0]
                            · linarith only [h179, h6, hlam]
                          · have p158_0 := h158c.1
                            have p158_1 := h158c.2.1
                            have p158_2 := h158c.2.2.1
                            have p158_3 := h158c.2.2.2
                            rcases p158_3 (m.d 0 3) (by simp) with h186 | h186
                            · rcases p158_3 (m.d 1 3) (by simp) with h187 | h187
                              · rcases p158_3 (m.d 2 3) (by simp) with h188 | h188
                                · linarith only [h188, h9, hlam]
                                · linarith only [h188, h97, hlam]
                              · linarith only [h187, hlam, p158_0]
                            · linarith only [h186, h7, hlam]
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
                            linarith only [h0, h13, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
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
                rcases p102_3 (m.d 0 1) (by simp) with h219 | h219
                · rcases p102_3 (m.d 1 2) (by simp) with h220 | h220
                  · rcases p102_3 (m.d 1 3) (by simp) with h221 | h221
                    · rcases p102_3 (m.d 1 4) (by simp) with h222 | h222
                      · linarith only [h14, h222, hlam]
                      · rcases p102_3 (m.d 1 5) (by simp) with h224 | h224
                        · rcases h3bigk with h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h0, h10, h13, h4, h96, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p102_1, p225_1]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            rcases p225_3 (m.d 0 3) (by simp) with h228 | h228
                            · rcases p225_3 (m.d 1 3) (by simp) with h229 | h229
                              · linarith only [h1, h229, hlam]
                              · linarith only [h229, h9, hlam]
                            · linarith only [h228, h4, hlam]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h10, h14, h6, h8, h96, hlam, p102_1, p225_2]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            rcases p225_3 (m.d 0 3) (by simp) with h234 | h234
                            · rcases p225_3 (m.d 1 3) (by simp) with h235 | h235
                              · linarith only [h1, h235, hlam]
                              · linarith only [h13, h235, hlam]
                            · linarith only [h234, hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h1, hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h1, h97, hc01, hc35, hlam, hphi, ht0b, ht5b, p225_1]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            rcases p225_3 (m.d 0 3) (by simp) with h242 | h242
                            · rcases p225_3 (m.d 1 3) (by simp) with h243 | h243
                              · rcases p225_3 (m.d 2 3) (by simp) with h244 | h244
                                · linarith only [h244, h9, hlam]
                                · linarith only [h244, h96, hlam]
                              · linarith only [h243, hlam, p225_0]
                            · linarith only [h242, h6, hlam]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            rcases p225_3 (m.d 0 3) (by simp) with h249 | h249
                            · rcases p225_3 (m.d 1 3) (by simp) with h250 | h250
                              · rcases p225_3 (m.d 2 3) (by simp) with h251 | h251
                                · linarith only [h251, h9, hlam]
                                · linarith only [h251, h97, hlam]
                              · linarith only [h250, hlam, p225_0]
                            · linarith only [h249, h7, hlam]
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
                            linarith only [hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p225_1]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h0, h100, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p225_1]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h6, hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h12, hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h96, hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h100, hlam, p225_1]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h7, hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h13, hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h97, hlam, p225_0]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [h0, h13, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p225_1]
                          · have p225_0 := h225c.1
                            have p225_1 := h225c.2.1
                            have p225_2 := h225c.2.2.1
                            have p225_3 := h225c.2.2.2
                            linarith only [hlam, p225_0]
                        · linarith only [h14, h224, hlam]
                    · linarith only [h12, h221, hlam]
                  · linarith only [h10, h220, hlam]
                · linarith only [h2, h219, hlam]
              · have p102_0 := h102c.1
                have p102_1 := h102c.2.1
                have p102_2 := h102c.2.2.1
                have p102_3 := h102c.2.2.2
                linarith only [hlam, p102_0]
        · linarith only [h0, h13, h9, h96, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
        · linarith only [h0, h12, h277, h9, h96, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h279 | h279
          · linarith only [h0, h12, h14, h279, h5, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h281 | h281
            · linarith only [h12, h14, h281, hlam]
            · rcases h1bigk with h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h12, h9, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h12, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                rcases p283_3 (m.d 0 1) (by simp) with h287 | h287
                · rcases p283_3 (m.d 1 2) (by simp) with h288 | h288
                  · linarith only [h0, h288, hlam]
                  · linarith only [h10, h288, hlam]
                · linarith only [h287, hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                rcases p283_3 (m.d 0 1) (by simp) with h292 | h292
                · rcases p283_3 (m.d 1 2) (by simp) with h293 | h293
                  · linarith only [h0, h293, hlam]
                  · linarith only [h11, h293, hlam]
                · linarith only [h292, hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h0, hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h13, h281, h96, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h0, h12, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h0, h13, h281, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h1, hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h9, hlam, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h1, h12, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h0, h13, h281, h9, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h2, hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h10, hlam, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h12, hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h14, hlam, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h3, hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h11, hlam, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h13, hlam, p283_0]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [h12, h3, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
              · have p283_0 := h283c.1
                have p283_1 := h283c.2.1
                have p283_2 := h283c.2.2.1
                have p283_3 := h283c.2.2.2
                linarith only [hlam, p283_0]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h317 | h317
    · linarith only [h12, h13, h317, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
      · rcases m.htr 2 3 5 (by decide) (by decide) with h320 | h320
        · linarith only [h13, h320, h9, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h322 | h322
          · linarith only [h10, h317, h322, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h324 | h324
            · linarith only [h10, h13, h317, h319, h324, h9, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · rcases h1bigk with h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h319, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                rcases p326_3 (m.d 0 1) (by simp) with h329 | h329
                · rcases p326_3 (m.d 1 2) (by simp) with h330 | h330
                  · linarith only [h0, h330, hlam]
                  · linarith only [h330, h9, hlam]
                · linarith only [h329, hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                rcases p326_3 (m.d 0 1) (by simp) with h334 | h334
                · rcases p326_3 (m.d 1 2) (by simp) with h335 | h335
                  · linarith only [h0, h335, hlam]
                  · linarith only [h10, h335, hlam]
                · linarith only [h334, hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                rcases p326_3 (m.d 0 1) (by simp) with h339 | h339
                · rcases p326_3 (m.d 1 2) (by simp) with h340 | h340
                  · linarith only [h0, h340, hlam]
                  · linarith only [h11, h340, hlam]
                · linarith only [h339, hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h0, hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h0, h319, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                rcases p326_3 (m.d 0 1) (by simp) with h347 | h347
                · rcases p326_3 (m.d 1 2) (by simp) with h348 | h348
                  · rcases p326_3 (m.d 1 3) (by simp) with h349 | h349
                    · linarith only [h349, h9, hlam]
                    · linarith only [h12, h349, hlam]
                  · linarith only [h10, h348, hlam]
                · linarith only [h2, h347, hlam]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h0, h13, h319, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h1, hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h9, hlam, p326_1]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h0, h10, h13, h319, h324, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h13, hlam, p326_1]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h2, hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h10, hlam, p326_1]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h12, hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h317, hlam, p326_1]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h3, hlam, p326_0]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h11, hlam, p326_1]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [h3, h319, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                rcases p326_3 (m.d 0 1) (by simp) with h368 | h368
                · rcases p326_3 (m.d 1 2) (by simp) with h369 | h369
                  · rcases p326_3 (m.d 1 3) (by simp) with h370 | h370
                    · linarith only [h13, h370, hlam]
                    · linarith only [h12, h370, hlam]
                  · linarith only [h10, h369, hlam]
                · linarith only [h2, h368, hlam]
              · have p326_0 := h326c.1
                have p326_1 := h326c.2.1
                have p326_2 := h326c.2.2.1
                have p326_3 := h326c.2.2.2
                linarith only [hlam, p326_0]
      · linarith only [h12, h13, h319, hc23, hc35, hlam, hphi]

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (h12 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h377 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 4 5 (by decide) (by decide) with h378 | h378
  · rcases m.htr 2 3 4 (by decide) (by decide) with h379 | h379
    · linarith only [h0, h12, h377, h379, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
      · rcases m.htr 2 4 5 (by decide) (by decide) with h382 | h382
        · rcases m.htr 3 4 5 (by decide) (by decide) with h383 | h383
          · rcases h1bigk with h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h381, h383, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              rcases p384_3 (m.d 0 1) (by simp) with h387 | h387
              · rcases p384_3 (m.d 1 2) (by simp) with h388 | h388
                · linarith only [h0, h388, hlam]
                · linarith only [h388, h9, hlam]
              · linarith only [h387, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              rcases p384_3 (m.d 0 1) (by simp) with h392 | h392
              · rcases p384_3 (m.d 1 2) (by simp) with h393 | h393
                · linarith only [h0, h393, hlam]
                · linarith only [h10, h393, hlam]
              · linarith only [h392, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              rcases p384_3 (m.d 0 1) (by simp) with h397 | h397
              · rcases p384_3 (m.d 1 2) (by simp) with h398 | h398
                · linarith only [h0, h398, hlam]
                · linarith only [h11, h398, hlam]
              · linarith only [h397, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h0, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h0, h381, h383, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h0, h12, h381, h383, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              rcases p384_3 (m.d 0 1) (by simp) with h406 | h406
              · rcases p384_3 (m.d 1 2) (by simp) with h407 | h407
                · rcases p384_3 (m.d 1 3) (by simp) with h408 | h408
                  · linarith only [h408, h9, hlam]
                  · linarith only [h377, h408, hlam]
                · linarith only [h11, h407, hlam]
              · linarith only [h3, h406, hlam]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h1, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h9, hlam, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h12, hlam, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h0, h11, h12, h4, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h2, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h10, hlam, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h2, h381, h383, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              rcases p384_3 (m.d 0 1) (by simp) with h422 | h422
              · rcases p384_3 (m.d 1 2) (by simp) with h423 | h423
                · rcases p384_3 (m.d 1 3) (by simp) with h424 | h424
                  · linarith only [h12, h424, hlam]
                  · linarith only [h377, h424, hlam]
                · linarith only [h11, h423, hlam]
              · linarith only [h3, h422, hlam]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h3, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h11, hlam, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h377, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h378, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [hlam, p384_0]
          · linarith only [h0, h12, h381, h383, h4, h6, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h12, h377, h378, h379, h381, h382, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · linarith only [h0, h12, h377, h381, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · linarith only [h12, h377, h378, hlam]

end R2N4
