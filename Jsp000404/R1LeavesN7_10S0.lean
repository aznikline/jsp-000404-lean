import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
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
              linarith only [h0, h13, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p20_1]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              rcases p20_3 (m.d 0 2) (by simp) with h23 | h23
              · rcases p20_3 (m.d 1 2) (by simp) with h24 | h24
                · linarith only [h0, h24, hlam]
                · linarith only [h24, h7, hlam]
              · linarith only [h23, hlam, p20_0]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              rcases p20_3 (m.d 0 2) (by simp) with h28 | h28
              · rcases p20_3 (m.d 1 2) (by simp) with h29 | h29
                · linarith only [h0, h29, hlam]
                · linarith only [h29, h8, hlam]
              · linarith only [h28, hlam, p20_0]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              rcases p20_3 (m.d 0 2) (by simp) with h33 | h33
              · rcases p20_3 (m.d 1 2) (by simp) with h34 | h34
                · linarith only [h0, h34, hlam]
                · linarith only [h34, h9, hlam]
              · linarith only [h33, hlam, p20_0]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              linarith only [h0, hlam, p20_1]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              linarith only [hlam, p20_0]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              linarith only [h0, h13, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              rcases p20_3 (m.d 0 2) (by simp) with h41 | h41
              · rcases p20_3 (m.d 1 2) (by simp) with h42 | h42
                · rcases p20_3 (m.d 2 3) (by simp) with h43 | h43
                  · linarith only [h43, h7, hlam]
                  · linarith only [h12, h43, hlam]
                · linarith only [h42, hlam, p20_0]
              · linarith only [h3, h41, hlam]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              rcases p20_3 (m.d 0 2) (by simp) with h48 | h48
              · rcases p20_3 (m.d 1 2) (by simp) with h49 | h49
                · rcases p20_3 (m.d 2 3) (by simp) with h50 | h50
                  · linarith only [h50, h7, hlam]
                  · linarith only [h13, h50, hlam]
                · linarith only [h49, hlam, p20_0]
              · linarith only [h4, h48, hlam]
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
              linarith only [h0, h12, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
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
              linarith only [h12, hlam, p20_0]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              linarith only [hlam, p20_0]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              linarith only [h14, hlam, p20_0]
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
              linarith only [h13, hlam, p20_0]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              linarith only [h0, h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
            · have p20_0 := h20c.1
              have p20_1 := h20c.2.1
              have p20_2 := h20c.2.2.1
              have p20_3 := h20c.2.2.2
              linarith only [hlam, p20_0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
        · linarith only [h12, h13, h70, hlam]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
          · linarith only [h0, h10, h7, h70, h72, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h11, h12, h13, h7, h72, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
      · linarith only [h0, h10, h12, h7, h75, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
        · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
          · rcases h2bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h0, h10, h7, h75, h78, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p79_1]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              rcases p79_3 (m.d 0 2) (by simp) with h82 | h82
              · rcases p79_3 (m.d 1 2) (by simp) with h83 | h83
                · linarith only [h0, h83, hlam]
                · linarith only [h7, h83, hlam]
              · linarith only [h82, hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              rcases p79_3 (m.d 0 2) (by simp) with h87 | h87
              · rcases p79_3 (m.d 1 2) (by simp) with h88 | h88
                · linarith only [h0, h88, hlam]
                · linarith only [h8, h88, hlam]
              · linarith only [h87, hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              rcases p79_3 (m.d 0 2) (by simp) with h92 | h92
              · rcases p79_3 (m.d 1 2) (by simp) with h93 | h93
                · linarith only [h0, h93, hlam]
                · linarith only [h9, h93, hlam]
              · linarith only [h92, hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h0, hlam, p79_1]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              rcases p79_3 (m.d 0 2) (by simp) with h99 | h99
              · rcases p79_3 (m.d 1 2) (by simp) with h100 | h100
                · rcases p79_3 (m.d 2 3) (by simp) with h101 | h101
                  · linarith only [h101, hlam, p79_0]
                  · rcases p79_3 (m.d 2 4) (by simp) with h103 | h103
                    · linarith only [h103, h8, hlam]
                    · linarith only [h103, h12, hlam]
                · linarith only [h100, hlam, p79_0]
              · linarith only [h2, h99, hlam]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h0, h77, hc01, hc45, hlam, hphi, ht0b, ht5b, p79_1]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              rcases p79_3 (m.d 0 2) (by simp) with h109 | h109
              · rcases p79_3 (m.d 1 2) (by simp) with h110 | h110
                · rcases p79_3 (m.d 2 3) (by simp) with h111 | h111
                  · linarith only [h111, h7, hlam]
                  · rcases p79_3 (m.d 2 4) (by simp) with h113 | h113
                    · linarith only [h113, h8, hlam]
                    · linarith only [h113, h77, hlam]
                · linarith only [h110, hlam, p79_0]
              · linarith only [h109, h4, hlam]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h2, hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h7, hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h12, hlam, p79_1]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h75, hlam, p79_1]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h3, hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h8, hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p79_1]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h0, h10, h12, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p79_1]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h4, hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h9, hlam, p79_0]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p79_1]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [h77, hlam, p79_1]
            · have p79_0 := h79c.1
              have p79_1 := h79c.2.1
              have p79_2 := h79c.2.2.1
              have p79_3 := h79c.2.2.2
              linarith only [hlam, p79_0]
          · linarith only [h0, h10, h11, h12, h7, h78, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
          · linarith only [h0, h10, h134, h7, h77, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h11, h12, h134, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
    · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
      · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
        · linarith only [h0, h11, h139, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
          · linarith only [h11, h137, h141, h8, hlam]
          · rcases h2bigk with h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h0, h138, h141, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              rcases p143_3 (m.d 0 2) (by simp) with h146 | h146
              · rcases p143_3 (m.d 1 2) (by simp) with h147 | h147
                · linarith only [h0, h147, hlam]
                · linarith only [h147, h7, hlam]
              · linarith only [h146, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              rcases p143_3 (m.d 0 2) (by simp) with h151 | h151
              · rcases p143_3 (m.d 1 2) (by simp) with h152 | h152
                · linarith only [h0, h152, hlam]
                · linarith only [h152, h8, hlam]
              · linarith only [h151, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              rcases p143_3 (m.d 0 2) (by simp) with h156 | h156
              · rcases p143_3 (m.d 1 2) (by simp) with h157 | h157
                · linarith only [h0, h157, hlam]
                · linarith only [h157, h9, hlam]
              · linarith only [h156, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h0, hlam, p143_1]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h0, h138, h141, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              rcases p143_3 (m.d 0 2) (by simp) with h164 | h164
              · rcases p143_3 (m.d 1 2) (by simp) with h165 | h165
                · rcases p143_3 (m.d 2 3) (by simp) with h166 | h166
                  · linarith only [h166, h7, hlam]
                  · linarith only [h137, h166, hlam]
                · linarith only [h165, hlam, p143_0]
              · linarith only [h164, h3, hlam]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              rcases p143_3 (m.d 0 2) (by simp) with h171 | h171
              · rcases p143_3 (m.d 1 2) (by simp) with h172 | h172
                · rcases p143_3 (m.d 2 3) (by simp) with h173 | h173
                  · linarith only [h173, h7, hlam]
                  · linarith only [h138, h173, hlam]
                · linarith only [h172, hlam, p143_0]
              · linarith only [h171, h4, hlam]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h2, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h7, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h0, h137, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h0, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p143_1]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h3, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h8, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h137, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h139, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h4, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h9, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h138, hlam, p143_0]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [h0, h137, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
            · have p143_0 := h143c.1
              have p143_1 := h143c.2.1
              have p143_2 := h143c.2.2.1
              have p143_3 := h143c.2.2.2
              linarith only [hlam, p143_0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h193 | h193
        · linarith only [h0, h11, h193, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h195 | h195
          · linarith only [h11, h137, h138, h195, h9, hlam]
          · rcases h2bigk with h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h0, h137, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              rcases p197_3 (m.d 0 2) (by simp) with h200 | h200
              · rcases p197_3 (m.d 1 2) (by simp) with h201 | h201
                · linarith only [h0, h201, hlam]
                · linarith only [h201, h7, hlam]
              · linarith only [h200, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              rcases p197_3 (m.d 0 2) (by simp) with h205 | h205
              · rcases p197_3 (m.d 1 2) (by simp) with h206 | h206
                · linarith only [h0, h206, hlam]
                · linarith only [h206, h8, hlam]
              · linarith only [h205, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              rcases p197_3 (m.d 0 2) (by simp) with h210 | h210
              · rcases p197_3 (m.d 1 2) (by simp) with h211 | h211
                · linarith only [h0, h211, hlam]
                · linarith only [h211, h9, hlam]
              · linarith only [h210, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h0, hlam, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h0, h137, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              rcases p197_3 (m.d 0 2) (by simp) with h218 | h218
              · rcases p197_3 (m.d 1 2) (by simp) with h219 | h219
                · rcases p197_3 (m.d 2 3) (by simp) with h220 | h220
                  · linarith only [h220, h7, hlam]
                  · linarith only [h137, h220, hlam]
                · linarith only [h219, hlam, p197_0]
              · linarith only [h218, h3, hlam]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h0, h137, h138, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h2, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h7, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h138, h195, h2, h5, h6, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h138, hlam, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h3, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h8, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h137, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h193, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h4, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h9, hlam, p197_0]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h0, h137, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [h0, h137, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p197_1]
            · have p197_0 := h197c.1
              have p197_1 := h197c.2.1
              have p197_2 := h197c.2.2.1
              have p197_3 := h197c.2.2.2
              linarith only [hlam, p197_0]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
      · linarith only [h0, h10, h137, h241, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h243 | h243
        · linarith only [h10, h11, h137, h243, hlam]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h245 | h245
          · linarith only [h10, h11, h245, hlam]
          · rcases h2bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h0, h10, h137, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h10, h11, h137, h2, h5, h6, hlam, p247_2]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              rcases p247_3 (m.d 0 2) (by simp) with h251 | h251
              · rcases p247_3 (m.d 1 2) (by simp) with h252 | h252
                · linarith only [h0, h252, hlam]
                · linarith only [h252, h8, hlam]
              · linarith only [h251, hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              rcases p247_3 (m.d 0 2) (by simp) with h256 | h256
              · rcases p247_3 (m.d 1 2) (by simp) with h257 | h257
                · linarith only [h0, h257, hlam]
                · linarith only [h257, h9, hlam]
              · linarith only [h256, hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h0, hlam, p247_1]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              rcases p247_3 (m.d 0 2) (by simp) with h263 | h263
              · rcases p247_3 (m.d 1 2) (by simp) with h264 | h264
                · rcases p247_3 (m.d 2 3) (by simp) with h265 | h265
                  · linarith only [h265, hlam, p247_0]
                  · rcases p247_3 (m.d 2 4) (by simp) with h267 | h267
                    · linarith only [h267, h8, hlam]
                    · linarith only [h137, h267, hlam]
                · linarith only [h264, hlam, p247_0]
              · linarith only [h2, h263, hlam]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              rcases p247_3 (m.d 0 2) (by simp) with h272 | h272
              · rcases p247_3 (m.d 1 2) (by simp) with h273 | h273
                · rcases p247_3 (m.d 2 3) (by simp) with h274 | h274
                  · linarith only [h274, h7, hlam]
                  · rcases p247_3 (m.d 2 4) (by simp) with h276 | h276
                    · linarith only [h276, hlam, p247_0]
                    · rcases p247_3 (m.d 2 5) (by simp) with h278 | h278
                      · linarith only [h278, h9, hlam]
                      · linarith only [h243, h278, hlam]
                · linarith only [h273, hlam, p247_0]
              · linarith only [h272, h3, hlam]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              rcases p247_3 (m.d 0 2) (by simp) with h283 | h283
              · rcases p247_3 (m.d 1 2) (by simp) with h284 | h284
                · rcases p247_3 (m.d 2 3) (by simp) with h285 | h285
                  · linarith only [h285, h7, hlam]
                  · rcases p247_3 (m.d 2 4) (by simp) with h287 | h287
                    · linarith only [h287, h8, hlam]
                    · rcases p247_3 (m.d 2 5) (by simp) with h289 | h289
                      · linarith only [h289, hlam, p247_0]
                      · rcases h4bigk with h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h0, h10, h137, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p291_1]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          rcases p291_3 (m.d 0 4) (by simp) with h294 | h294
                          · rcases p291_3 (m.d 1 4) (by simp) with h295 | h295
                            · linarith only [h1, h295, hlam]
                            · linarith only [h295, h8, hlam]
                          · linarith only [h294, h3, hlam]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h0, h137, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p291_1]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h0, h10, h11, h137, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p291_1]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h1, hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h11, h137, h6, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p291_1]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h0, h11, h137, h2, h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p291_1]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h11, hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h3, hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h8, hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h137, hlam, p291_1]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h243, hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h5, hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h10, hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h10, h137, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p291_1]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h245, hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h6, hlam, p291_0]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h0, h2, h5, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p291_1]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h0, h137, h2, h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p291_1]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [h0, h2, h5, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p291_1]
                        · have p291_0 := h291c.1
                          have p291_1 := h291c.2.1
                          have p291_2 := h291c.2.2.1
                          have p291_3 := h291c.2.2.2
                          linarith only [hlam, p291_0]
                · linarith only [h284, hlam, p247_0]
              · linarith only [h283, h4, hlam]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h2, hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h7, hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h137, hlam, p247_1]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h241, hlam, p247_1]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h3, hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h8, hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h243, hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h4, hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h9, hlam, p247_0]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [h0, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p247_1]
            · have p247_0 := h247c.1
              have p247_1 := h247c.2.1
              have p247_2 := h247c.2.2.1
              have p247_3 := h247c.2.2.2
              linarith only [hlam, p247_0]

end R2N4
