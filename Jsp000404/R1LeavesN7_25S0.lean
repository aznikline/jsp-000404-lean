import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
    · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
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
                  linarith only [h0, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p20_1]
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
                  linarith only [h0, h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                · have p20_0 := h20c.1
                  have p20_1 := h20c.2.1
                  have p20_2 := h20c.2.2.1
                  have p20_3 := h20c.2.2.2
                  linarith only [hlam, p20_0]
          · linarith only [h0, h11, h12, h13, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
          · linarith only [h0, h10, h12, h7, h71, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h73 | h73
            · rcases m.htr 3 4 5 (by decide) (by decide) with h74 | h74
              · rcases h2bigk with h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h0, h10, h7, h71, h74, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p75_1]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  rcases p75_3 (m.d 0 2) (by simp) with h78 | h78
                  · rcases p75_3 (m.d 1 2) (by simp) with h79 | h79
                    · linarith only [h0, h79, hlam]
                    · linarith only [h7, h79, hlam]
                  · linarith only [h78, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  rcases p75_3 (m.d 0 2) (by simp) with h83 | h83
                  · rcases p75_3 (m.d 1 2) (by simp) with h84 | h84
                    · linarith only [h0, h84, hlam]
                    · linarith only [h8, h84, hlam]
                  · linarith only [h83, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  rcases p75_3 (m.d 0 2) (by simp) with h88 | h88
                  · rcases p75_3 (m.d 1 2) (by simp) with h89 | h89
                    · linarith only [h0, h89, hlam]
                    · linarith only [h89, h9, hlam]
                  · linarith only [h88, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h0, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  rcases p75_3 (m.d 0 2) (by simp) with h95 | h95
                  · rcases p75_3 (m.d 1 2) (by simp) with h96 | h96
                    · rcases p75_3 (m.d 2 3) (by simp) with h97 | h97
                      · linarith only [h97, hlam, p75_0]
                      · rcases p75_3 (m.d 2 4) (by simp) with h99 | h99
                        · linarith only [h8, h99, hlam]
                        · linarith only [h12, h99, hlam]
                    · linarith only [h96, hlam, p75_0]
                  · linarith only [h2, h95, hlam]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h0, h73, hc01, hc45, hlam, hphi, ht0b, ht5b, p75_1]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  rcases p75_3 (m.d 0 2) (by simp) with h105 | h105
                  · rcases p75_3 (m.d 1 2) (by simp) with h106 | h106
                    · rcases p75_3 (m.d 2 3) (by simp) with h107 | h107
                      · linarith only [h107, h7, hlam]
                      · rcases p75_3 (m.d 2 4) (by simp) with h109 | h109
                        · linarith only [h109, h8, hlam]
                        · linarith only [h109, h73, hlam]
                    · linarith only [h106, hlam, p75_0]
                  · linarith only [h105, h4, hlam]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h2, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h7, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h12, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h71, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h3, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h8, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p75_1]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h1, h10, h12, hc01, hc25, hlam, hphi, ht0b, ht5b, p75_1]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h4, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h9, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p75_1]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [h73, hlam, p75_0]
                · have p75_0 := h75c.1
                  have p75_1 := h75c.2.1
                  have p75_2 := h75c.2.2.1
                  have p75_3 := h75c.2.2.2
                  linarith only [hlam, p75_0]
              · linarith only [h12, h73, h74, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
              · linarith only [h0, h10, h130, h7, h73, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h2bigk with h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h0, h10, h12, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p132_1]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  rcases p132_3 (m.d 0 2) (by simp) with h135 | h135
                  · rcases p132_3 (m.d 1 2) (by simp) with h136 | h136
                    · linarith only [h0, h136, hlam]
                    · linarith only [h136, h7, hlam]
                  · linarith only [h135, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  rcases p132_3 (m.d 0 2) (by simp) with h140 | h140
                  · rcases p132_3 (m.d 1 2) (by simp) with h141 | h141
                    · linarith only [h0, h141, hlam]
                    · linarith only [h141, h8, hlam]
                  · linarith only [h140, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  rcases p132_3 (m.d 0 2) (by simp) with h145 | h145
                  · rcases p132_3 (m.d 1 2) (by simp) with h146 | h146
                    · linarith only [h0, h146, hlam]
                    · linarith only [h146, h9, hlam]
                  · linarith only [h145, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h0, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  rcases p132_3 (m.d 0 2) (by simp) with h152 | h152
                  · rcases p132_3 (m.d 1 2) (by simp) with h153 | h153
                    · rcases p132_3 (m.d 2 3) (by simp) with h154 | h154
                      · linarith only [h154, hlam, p132_0]
                      · rcases p132_3 (m.d 2 4) (by simp) with h156 | h156
                        · linarith only [h156, h8, hlam]
                        · linarith only [h12, h156, hlam]
                    · linarith only [h153, hlam, p132_0]
                  · linarith only [h152, h2, hlam]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  rcases p132_3 (m.d 0 2) (by simp) with h161 | h161
                  · rcases p132_3 (m.d 1 2) (by simp) with h162 | h162
                    · rcases p132_3 (m.d 2 3) (by simp) with h163 | h163
                      · linarith only [h163, h7, hlam]
                      · rcases p132_3 (m.d 2 4) (by simp) with h165 | h165
                        · linarith only [h165, hlam, p132_0]
                        · rcases p132_3 (m.d 2 5) (by simp) with h167 | h167
                          · linarith only [h167, h9, hlam]
                          · linarith only [h167, h73, hlam]
                    · linarith only [h162, hlam, p132_0]
                  · linarith only [h161, h3, hlam]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  rcases p132_3 (m.d 0 2) (by simp) with h172 | h172
                  · rcases p132_3 (m.d 1 2) (by simp) with h173 | h173
                    · rcases p132_3 (m.d 2 3) (by simp) with h174 | h174
                      · linarith only [h174, h7, hlam]
                      · rcases p132_3 (m.d 2 4) (by simp) with h176 | h176
                        · linarith only [h176, h8, hlam]
                        · rcases p132_3 (m.d 2 5) (by simp) with h178 | h178
                          · linarith only [h178, hlam, p132_0]
                          · rcases h3bigk with h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h11, h12, h130, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p180_1]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              rcases p180_3 (m.d 0 3) (by simp) with h183 | h183
                              · rcases p180_3 (m.d 1 3) (by simp) with h184 | h184
                                · linarith only [h1, h184, hlam]
                                · linarith only [h184, h7, hlam]
                              · linarith only [h183, h2, hlam]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h0, h12, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p180_1]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h0, h12, h130, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p180_1]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h1, hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p180_1]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h0, h12, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p180_1]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h0, h12, h130, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p180_1]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h2, hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h7, hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h12, hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h71, hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h5, hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h10, hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [hc23, hc34, hlam, hphi, p180_1]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h130, hlam, p180_1]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h6, hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h11, hlam, p180_0]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h0, h11, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p180_1]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [h0, h11, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p180_1]
                            · have p180_0 := h180c.1
                              have p180_1 := h180c.2.1
                              have p180_2 := h180c.2.2.1
                              have p180_3 := h180c.2.2.2
                              linarith only [hlam, p180_0]
                    · linarith only [h173, hlam, p132_0]
                  · linarith only [h172, h4, hlam]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h2, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h7, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h12, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h71, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h3, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h8, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p132_1]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h73, hlam, p132_1]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h4, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h9, hlam, p132_0]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p132_1]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [h0, h11, h7, h71, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                · have p132_0 := h132c.1
                  have p132_1 := h132c.2.1
                  have p132_2 := h132c.2.2.1
                  have p132_3 := h132c.2.2.2
                  linarith only [hlam, p132_0]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
        · rcases m.htr 2 3 5 (by decide) (by decide) with h228 | h228
          · linarith only [h11, h228, h7, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h230 | h230
            · linarith only [h227, h228, h230, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h232 | h232
              · linarith only [h0, h2, h227, h230, h232, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h2bigk with h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h0, h227, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p234_1]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  rcases p234_3 (m.d 0 2) (by simp) with h237 | h237
                  · rcases p234_3 (m.d 1 2) (by simp) with h238 | h238
                    · linarith only [h0, h238, hlam]
                    · linarith only [h238, h7, hlam]
                  · linarith only [h237, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  rcases p234_3 (m.d 0 2) (by simp) with h242 | h242
                  · rcases p234_3 (m.d 1 2) (by simp) with h243 | h243
                    · linarith only [h0, h243, hlam]
                    · linarith only [h243, h8, hlam]
                  · linarith only [h242, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  rcases p234_3 (m.d 0 2) (by simp) with h247 | h247
                  · rcases p234_3 (m.d 1 2) (by simp) with h248 | h248
                    · linarith only [h0, h248, hlam]
                    · linarith only [h248, h9, hlam]
                  · linarith only [h247, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h0, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h0, h227, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p234_1]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  rcases p234_3 (m.d 0 2) (by simp) with h255 | h255
                  · rcases p234_3 (m.d 1 2) (by simp) with h256 | h256
                    · rcases p234_3 (m.d 2 3) (by simp) with h257 | h257
                      · linarith only [h257, h7, hlam]
                      · linarith only [h227, h257, hlam]
                    · linarith only [h256, hlam, p234_0]
                  · linarith only [h255, h3, hlam]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h0, h227, h228, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p234_1]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h2, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h7, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h0, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p234_1]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h228, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h3, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h8, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h227, hlam, p234_1]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h230, hlam, p234_1]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h4, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h9, hlam, p234_0]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p234_1]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [h0, h227, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p234_1]
                · have p234_0 := h234c.1
                  have p234_1 := h234c.2.1
                  have p234_2 := h234c.2.2.1
                  have p234_3 := h234c.2.2.2
                  linarith only [hlam, p234_0]
        · linarith only [h0, h10, h11, h2, h227, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
      · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
        · linarith only [h0, h10, h2, h279, h280, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
          · rcases m.htr 2 4 5 (by decide) (by decide) with h283 | h283
            · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
              · rcases h2bigk with h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h282, h284, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  rcases p285_3 (m.d 0 2) (by simp) with h288 | h288
                  · rcases p285_3 (m.d 1 2) (by simp) with h289 | h289
                    · linarith only [h0, h289, hlam]
                    · linarith only [h289, h7, hlam]
                  · linarith only [h288, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  rcases p285_3 (m.d 0 2) (by simp) with h293 | h293
                  · rcases p285_3 (m.d 1 2) (by simp) with h294 | h294
                    · linarith only [h0, h294, hlam]
                    · linarith only [h294, h8, hlam]
                  · linarith only [h293, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  rcases p285_3 (m.d 0 2) (by simp) with h298 | h298
                  · rcases p285_3 (m.d 1 2) (by simp) with h299 | h299
                    · linarith only [h0, h299, hlam]
                    · linarith only [h299, h9, hlam]
                  · linarith only [h298, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h282, h284, hc01, hc45, hlam, hphi, ht0b, ht5b, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h280, h282, h284, hc01, hc45, hlam, hphi, ht0b, ht5b, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  rcases p285_3 (m.d 0 2) (by simp) with h307 | h307
                  · rcases p285_3 (m.d 1 2) (by simp) with h308 | h308
                    · rcases p285_3 (m.d 2 3) (by simp) with h309 | h309
                      · linarith only [h309, h7, hlam]
                      · linarith only [h282, h309, hlam]
                    · linarith only [h308, hlam, p285_0]
                  · linarith only [h307, h4, hlam]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h2, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h7, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h280, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h10, h2, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h3, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h8, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h282, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h282, h284, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h4, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h9, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h282, hlam, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h283, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hlam, p285_0]
              · linarith only [h0, h10, h282, h283, h284, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h280, h282, h283, hlam]
          · linarith only [h10, h279, h282, hc23, hc34, hlam, hphi]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h332 | h332
        · linarith only [h0, h10, h332, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h334 | h334
          · linarith only [h279, h334, h7, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h336 | h336
            · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
              · rcases h2bigk with h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h0, h336, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p338_1]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  rcases p338_3 (m.d 0 2) (by simp) with h341 | h341
                  · rcases p338_3 (m.d 1 2) (by simp) with h342 | h342
                    · linarith only [h0, h342, hlam]
                    · linarith only [h342, h7, hlam]
                  · linarith only [h341, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  rcases p338_3 (m.d 0 2) (by simp) with h346 | h346
                  · rcases p338_3 (m.d 1 2) (by simp) with h347 | h347
                    · linarith only [h0, h347, hlam]
                    · linarith only [h347, h8, hlam]
                  · linarith only [h346, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  rcases p338_3 (m.d 0 2) (by simp) with h351 | h351
                  · rcases p338_3 (m.d 1 2) (by simp) with h352 | h352
                    · linarith only [h0, h352, hlam]
                    · linarith only [h352, h9, hlam]
                  · linarith only [h351, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h0, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  rcases p338_3 (m.d 0 2) (by simp) with h358 | h358
                  · rcases p338_3 (m.d 1 2) (by simp) with h359 | h359
                    · rcases p338_3 (m.d 2 3) (by simp) with h360 | h360
                      · linarith only [h360, hlam, p338_0]
                      · rcases p338_3 (m.d 2 4) (by simp) with h362 | h362
                        · linarith only [h362, h8, hlam]
                        · linarith only [h332, h362, hlam]
                    · linarith only [h359, hlam, p338_0]
                  · linarith only [h2, h358, hlam]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h0, h336, hc01, hc45, hlam, hphi, ht0b, ht5b, p338_1]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  rcases p338_3 (m.d 0 2) (by simp) with h368 | h368
                  · rcases p338_3 (m.d 1 2) (by simp) with h369 | h369
                    · rcases p338_3 (m.d 2 3) (by simp) with h370 | h370
                      · linarith only [h370, h7, hlam]
                      · rcases p338_3 (m.d 2 4) (by simp) with h372 | h372
                        · linarith only [h372, h8, hlam]
                        · linarith only [h336, h372, hlam]
                    · linarith only [h369, hlam, p338_0]
                  · linarith only [h368, h4, hlam]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h2, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h7, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h332, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h334, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h3, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h8, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p338_1]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h0, h334, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p338_1]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h4, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h9, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p338_1]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [h336, hlam, p338_0]
                · have p338_0 := h338c.1
                  have p338_1 := h338c.2.1
                  have p338_2 := h338c.2.2.1
                  have p338_3 := h338c.2.2.2
                  linarith only [hlam, p338_0]
              · linarith only [h0, h10, h336, h337, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h393 | h393
              · rcases h2bigk with h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  rcases p394_3 (m.d 0 2) (by simp) with h396 | h396
                  · rcases p394_3 (m.d 1 2) (by simp) with h397 | h397
                    · linarith only [h0, h397, hlam]
                    · rcases p394_3 (m.d 2 3) (by simp) with h399 | h399
                      · linarith only [h2, h399, hlam]
                      · rcases p394_3 (m.d 2 4) (by simp) with h401 | h401
                        · linarith only [h3, h401, hlam]
                        · rcases p394_3 (m.d 2 5) (by simp) with h403 | h403
                          · linarith only [h4, h403, hlam]
                          · rcases h3bigk with h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              rcases p405_3 (m.d 0 3) (by simp) with h407 | h407
                              · rcases p405_3 (m.d 1 3) (by simp) with h408 | h408
                                · linarith only [h1, h408, hlam]
                                · rcases p405_3 (m.d 2 3) (by simp) with h410 | h410
                                  · linarith only [h2, h410, hlam]
                                  · rcases p405_3 (m.d 3 4) (by simp) with h412 | h412
                                    · linarith only [h412, h5, hlam]
                                    · linarith only [h10, h412, hlam]
                              · linarith only [h1, h407, hlam]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              rcases p405_3 (m.d 0 3) (by simp) with h416 | h416
                              · rcases p405_3 (m.d 1 3) (by simp) with h417 | h417
                                · linarith only [h1, h417, hlam]
                                · linarith only [h417, h7, hlam]
                              · linarith only [h2, h416, hlam]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h0, h10, h2, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p405_1]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h0, h2, h332, h336, h393, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p405_1]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h1, hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p405_1]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h10, hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h279, hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h2, hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h7, hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h332, hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h334, hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h5, hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [hc13, hc34, hlam, hphi, p405_1]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h0, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p405_1]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h0, h2, h332, h336, h393, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p405_1]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h6, hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h7, hc23, hc35, hlam, hphi, p405_1]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h0, h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p405_1]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [h393, hlam, p405_0]
                            · have p405_0 := h405c.1
                              have p405_1 := h405c.2.1
                              have p405_2 := h405c.2.2.1
                              have p405_3 := h405c.2.2.2
                              linarith only [hlam, p405_0]
                  · linarith only [h0, h396, hlam]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h2, h332, h336, h393, h5, hlam, p394_2]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h2, h336, h393, h5, hlam, p394_2]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  rcases p394_3 (m.d 0 2) (by simp) with h446 | h446
                  · rcases p394_3 (m.d 1 2) (by simp) with h447 | h447
                    · linarith only [h0, h447, hlam]
                    · linarith only [h447, h9, hlam]
                  · linarith only [h446, hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h0, hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  rcases p394_3 (m.d 0 2) (by simp) with h453 | h453
                  · rcases p394_3 (m.d 1 2) (by simp) with h454 | h454
                    · rcases p394_3 (m.d 2 3) (by simp) with h455 | h455
                      · linarith only [h455, hlam, p394_0]
                      · rcases p394_3 (m.d 2 4) (by simp) with h457 | h457
                        · linarith only [h457, h8, hlam]
                        · linarith only [h332, h457, hlam]
                    · linarith only [h454, hlam, p394_0]
                  · linarith only [h2, h453, hlam]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  rcases p394_3 (m.d 0 2) (by simp) with h462 | h462
                  · rcases p394_3 (m.d 1 2) (by simp) with h463 | h463
                    · rcases p394_3 (m.d 2 3) (by simp) with h464 | h464
                      · linarith only [h464, h7, hlam]
                      · rcases p394_3 (m.d 2 4) (by simp) with h466 | h466
                        · linarith only [h466, hlam, p394_0]
                        · rcases p394_3 (m.d 2 5) (by simp) with h468 | h468
                          · linarith only [h468, h9, hlam]
                          · linarith only [h336, h468, hlam]
                    · linarith only [h463, hlam, p394_0]
                  · linarith only [h3, h462, hlam]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  rcases p394_3 (m.d 0 2) (by simp) with h473 | h473
                  · rcases p394_3 (m.d 1 2) (by simp) with h474 | h474
                    · rcases p394_3 (m.d 2 3) (by simp) with h475 | h475
                      · linarith only [h475, h7, hlam]
                      · rcases p394_3 (m.d 2 4) (by simp) with h477 | h477
                        · linarith only [h477, h8, hlam]
                        · rcases p394_3 (m.d 2 5) (by simp) with h479 | h479
                          · linarith only [h479, hlam, p394_0]
                          · rcases h3bigk with h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              rcases p481_3 (m.d 0 3) (by simp) with h483 | h483
                              · rcases p481_3 (m.d 1 3) (by simp) with h484 | h484
                                · linarith only [h1, h484, hlam]
                                · rcases p481_3 (m.d 2 3) (by simp) with h486 | h486
                                  · linarith only [h2, h486, hlam]
                                  · rcases p481_3 (m.d 3 4) (by simp) with h488 | h488
                                    · linarith only [h488, h5, hlam]
                                    · linarith only [h10, h488, hlam]
                              · linarith only [h1, h483, hlam]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              rcases p481_3 (m.d 0 3) (by simp) with h492 | h492
                              · rcases p481_3 (m.d 1 3) (by simp) with h493 | h493
                                · linarith only [h1, h493, hlam]
                                · linarith only [h493, h7, hlam]
                              · linarith only [h2, h492, hlam]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h0, h2, h332, h336, h393, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h0, h2, h279, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h1, hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h10, hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h279, hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h2, hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h7, hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h332, hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h334, hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h5, hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [hc13, hc34, hlam, hphi, p481_1]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h0, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h0, h2, h279, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h6, hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h7, hc23, hc35, hlam, hphi, p481_1]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h0, h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [h393, hlam, p481_0]
                            · have p481_0 := h481c.1
                              have p481_1 := h481c.2.1
                              have p481_2 := h481c.2.2.1
                              have p481_3 := h481c.2.2.2
                              linarith only [hlam, p481_0]
                    · linarith only [h474, hlam, p394_0]
                  · linarith only [h4, h473, hlam]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h2, hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h7, hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h332, hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h334, hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h3, hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h8, hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h336, hc23, hc45, hlam, hphi, ht34, p394_1]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h336, hlam, p394_1]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h4, hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h9, hlam, p394_0]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p394_1]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [h0, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p394_1]
                · have p394_0 := h394c.1
                  have p394_1 := h394c.2.1
                  have p394_2 := h394c.2.2.1
                  have p394_3 := h394c.2.2.2
                  linarith only [hlam, p394_0]
              · rcases h2bigk with h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  rcases p536_3 (m.d 0 2) (by simp) with h538 | h538
                  · rcases p536_3 (m.d 1 2) (by simp) with h539 | h539
                    · linarith only [h0, h539, hlam]
                    · rcases p536_3 (m.d 2 3) (by simp) with h541 | h541
                      · linarith only [h2, h541, hlam]
                      · rcases p536_3 (m.d 2 4) (by simp) with h543 | h543
                        · linarith only [h3, h543, hlam]
                        · rcases p536_3 (m.d 2 5) (by simp) with h545 | h545
                          · linarith only [h4, h545, hlam]
                          · rcases h3bigk with h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              rcases p547_3 (m.d 0 3) (by simp) with h549 | h549
                              · rcases p547_3 (m.d 1 3) (by simp) with h550 | h550
                                · linarith only [h1, h550, hlam]
                                · rcases p547_3 (m.d 2 3) (by simp) with h552 | h552
                                  · linarith only [h2, h552, hlam]
                                  · rcases p547_3 (m.d 3 4) (by simp) with h554 | h554
                                    · linarith only [h5, h554, hlam]
                                    · linarith only [h10, h554, hlam]
                              · linarith only [h1, h549, hlam]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              rcases p547_3 (m.d 0 3) (by simp) with h558 | h558
                              · rcases p547_3 (m.d 1 3) (by simp) with h559 | h559
                                · linarith only [h1, h559, hlam]
                                · linarith only [h559, h7, hlam]
                              · linarith only [h2, h558, hlam]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h0, h10, h2, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p547_1]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h0, h2, h279, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p547_1]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h1, hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h10, hc23, hc34, hlam, hphi, p547_1]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h10, hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h279, hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h2, hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h7, hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h332, hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h334, hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h5, hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [hc13, hc34, hlam, hphi, p547_1]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h0, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p547_1]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h393, hlam, p547_1]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h6, hlam, p547_0]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h7, hc23, hc35, hlam, hphi, p547_1]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h0, h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p547_1]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [h0, h2, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p547_1]
                            · have p547_0 := h547c.1
                              have p547_1 := h547c.2.1
                              have p547_2 := h547c.2.2.1
                              have p547_3 := h547c.2.2.2
                              linarith only [hlam, p547_0]
                  · linarith only [h0, h538, hlam]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  rcases p536_3 (m.d 0 2) (by simp) with h586 | h586
                  · rcases p536_3 (m.d 1 2) (by simp) with h587 | h587
                    · linarith only [h0, h587, hlam]
                    · linarith only [h587, h7, hlam]
                  · linarith only [h586, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  rcases p536_3 (m.d 0 2) (by simp) with h591 | h591
                  · rcases p536_3 (m.d 1 2) (by simp) with h592 | h592
                    · linarith only [h0, h592, hlam]
                    · linarith only [h592, h8, hlam]
                  · linarith only [h591, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  rcases p536_3 (m.d 0 2) (by simp) with h596 | h596
                  · rcases p536_3 (m.d 1 2) (by simp) with h597 | h597
                    · linarith only [h0, h597, hlam]
                    · linarith only [h597, h9, hlam]
                  · linarith only [h596, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h0, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  rcases p536_3 (m.d 0 2) (by simp) with h603 | h603
                  · rcases p536_3 (m.d 1 2) (by simp) with h604 | h604
                    · rcases p536_3 (m.d 2 3) (by simp) with h605 | h605
                      · linarith only [h605, hlam, p536_0]
                      · rcases p536_3 (m.d 2 4) (by simp) with h607 | h607
                        · linarith only [h607, h8, hlam]
                        · linarith only [h332, h607, hlam]
                    · linarith only [h604, hlam, p536_0]
                  · linarith only [h2, h603, hlam]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  rcases p536_3 (m.d 0 2) (by simp) with h612 | h612
                  · rcases p536_3 (m.d 1 2) (by simp) with h613 | h613
                    · rcases p536_3 (m.d 2 3) (by simp) with h614 | h614
                      · linarith only [h614, h7, hlam]
                      · rcases p536_3 (m.d 2 4) (by simp) with h616 | h616
                        · linarith only [h616, hlam, p536_0]
                        · rcases p536_3 (m.d 2 5) (by simp) with h618 | h618
                          · linarith only [h618, h9, hlam]
                          · linarith only [h336, h618, hlam]
                    · linarith only [h613, hlam, p536_0]
                  · linarith only [h3, h612, hlam]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  rcases p536_3 (m.d 0 2) (by simp) with h623 | h623
                  · rcases p536_3 (m.d 1 2) (by simp) with h624 | h624
                    · rcases p536_3 (m.d 2 3) (by simp) with h625 | h625
                      · linarith only [h625, h7, hlam]
                      · rcases p536_3 (m.d 2 4) (by simp) with h627 | h627
                        · linarith only [h627, h8, hlam]
                        · rcases p536_3 (m.d 2 5) (by simp) with h629 | h629
                          · linarith only [h629, hlam, p536_0]
                          · rcases h3bigk with h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              rcases p631_3 (m.d 0 3) (by simp) with h633 | h633
                              · rcases p631_3 (m.d 1 3) (by simp) with h634 | h634
                                · linarith only [h1, h634, hlam]
                                · rcases p631_3 (m.d 2 3) (by simp) with h636 | h636
                                  · linarith only [h2, h636, hlam]
                                  · rcases p631_3 (m.d 3 4) (by simp) with h638 | h638
                                    · linarith only [h5, h638, hlam]
                                    · linarith only [h10, h638, hlam]
                              · linarith only [h1, h633, hlam]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              rcases p631_3 (m.d 0 3) (by simp) with h642 | h642
                              · rcases p631_3 (m.d 1 3) (by simp) with h643 | h643
                                · linarith only [h1, h643, hlam]
                                · linarith only [h643, h7, hlam]
                              · linarith only [h2, h642, hlam]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h0, h10, h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p631_1]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h0, h2, h279, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p631_1]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h1, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h10, hc23, hc34, hlam, hphi, p631_1]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h10, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h279, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h2, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h7, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h332, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h334, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h5, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hc13, hc34, hlam, hphi, p631_1]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h0, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p631_1]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h393, hlam, p631_1]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h6, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h7, hc23, hc35, hlam, hphi, p631_1]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h0, h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p631_1]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h0, h10, h2, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p631_1]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hlam, p631_0]
                    · linarith only [h624, hlam, p536_0]
                  · linarith only [h4, h623, hlam]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h2, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h7, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h332, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h334, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h3, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h8, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h336, hlam, p536_1]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h4, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h9, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h0, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p536_1]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, p536_0]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h686 | h686
    · rcases m.htr 1 3 5 (by decide) (by decide) with h687 | h687
      · linarith only [h687, h7, h9, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h689 | h689
        · linarith only [h0, h4, h689, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h2, h6, h686, h687, h689, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h692 | h692
      · linarith only [h686, h692, h8, h9, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h694 | h694
        · linarith only [h0, h4, h686, h694, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h696 | h696
          · linarith only [h692, h696, h7, h9, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h698 | h698
            · linarith only [h0, h2, h6, h696, h698, h8, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h700 | h700
              · linarith only [h694, h698, h700, h8, h9, hc23, hc34, hlam, hphi]
              · rcases h2bigk with h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  rcases p702_3 (m.d 0 2) (by simp) with h704 | h704
                  · rcases p702_3 (m.d 1 2) (by simp) with h705 | h705
                    · linarith only [h0, h705, hlam]
                    · rcases p702_3 (m.d 2 3) (by simp) with h707 | h707
                      · linarith only [h2, h707, hlam]
                      · rcases p702_3 (m.d 2 4) (by simp) with h709 | h709
                        · linarith only [h3, h709, hlam]
                        · rcases p702_3 (m.d 2 5) (by simp) with h711 | h711
                          · linarith only [h4, h711, hlam]
                          · linarith only [h711, h9, hlam]
                  · linarith only [h0, h704, hlam]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h2, h6, h694, h696, h8, h9, hlam, p702_2]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h2, h6, h696, h8, h9, hlam, p702_2]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h0, h694, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p702_1]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h0, hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h696, h9, hc23, hc35, hlam, hphi, p702_1]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h0, h4, h694, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p702_1]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h9, hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h2, hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h7, hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h694, hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h696, hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h3, hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h8, hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h0, h4, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p702_1]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h698, hlam, p702_1]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h4, hlam, p702_0]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p702_1]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  rcases p702_3 (m.d 0 2) (by simp) with h735 | h735
                  · rcases p702_3 (m.d 1 2) (by simp) with h736 | h736
                    · linarith only [h736, h9, hlam]
                    · linarith only [h7, h736, hlam]
                  · linarith only [h2, h735, hlam]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  rcases p702_3 (m.d 0 2) (by simp) with h740 | h740
                  · rcases p702_3 (m.d 1 2) (by simp) with h741 | h741
                    · linarith only [h741, h9, hlam]
                    · linarith only [h741, h8, hlam]
                  · linarith only [h3, h740, hlam]
                · have p702_0 := h702c.1
                  have p702_1 := h702c.2.1
                  have p702_2 := h702c.2.2.1
                  have p702_3 := h702c.2.2.2
                  linarith only [hlam, p702_0]

end R2N4
