import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
  · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
    · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
      · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
        · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
          · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
            · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h16, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h0, h13, h15, h16, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h15, h19, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                · linarith only [h0, h10, h21, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                  · linarith only [h0, h12, h15, h21, h23, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h12, h14, h15, h23, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
            · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
              · linarith only [h0, h27, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h0, h13, h26, h27, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
              · linarith only [h0, h26, h30, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
                · linarith only [h12, h14, h26, h32, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                  · linarith only [h12, h14, h34, hlam]
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
                      linarith only [h13, h30, h9, hc01, hlam, hphi, ht0b, ht5b, p36_1, u5ehi2]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h13, h30, hc01, hlam, hphi, ht0b, ht5b, p36_1, u5ehi2]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      rcases p36_3 (m.d 0 1) (by simp) with h40 | h40
                      · rcases p36_3 (m.d 1 2) (by simp) with h41 | h41
                        · linarith only [h0, h41, hlam]
                        · linarith only [h10, h41, hlam]
                      · linarith only [h40, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      rcases p36_3 (m.d 0 1) (by simp) with h45 | h45
                      · rcases p36_3 (m.d 1 2) (by simp) with h46 | h46
                        · linarith only [h0, h46, hlam]
                        · linarith only [h11, h46, hlam]
                      · linarith only [h45, hlam, p36_0]
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
                      linarith only [h13, h26, h34, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h0, h12, h26, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p36_1, u5ehi1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h1, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h9, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h0, h12, h26, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h0, h11, h9, hc01, hlam, hphi, ht0b, ht5b, p36_1, u5ehi2]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h2, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h10, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h12, hlam, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h14, hlam, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h3, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h11, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h13, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h12, h26, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [hlam, p36_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
          · linarith only [h12, h13, h70, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
            · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
              · linarith only [h0, h73, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                · linarith only [h10, h70, h75, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                  · linarith only [h10, h12, h13, h70, h77, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases h1bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h11, hc01, hlam, hphi, ht0b, ht5b, p79_1, u5ehi2]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      rcases p79_3 (m.d 0 1) (by simp) with h82 | h82
                      · rcases p79_3 (m.d 1 2) (by simp) with h83 | h83
                        · linarith only [h0, h83, hlam]
                        · linarith only [h83, h9, hlam]
                      · linarith only [h82, hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      rcases p79_3 (m.d 0 1) (by simp) with h87 | h87
                      · rcases p79_3 (m.d 1 2) (by simp) with h88 | h88
                        · linarith only [h0, h88, hlam]
                        · linarith only [h10, h88, hlam]
                      · linarith only [h87, hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      rcases p79_3 (m.d 0 1) (by simp) with h92 | h92
                      · rcases p79_3 (m.d 1 2) (by simp) with h93 | h93
                        · linarith only [h0, h93, hlam]
                        · linarith only [h11, h93, hlam]
                      · linarith only [h92, hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h0, hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h0, h72, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      rcases p79_3 (m.d 0 1) (by simp) with h100 | h100
                      · rcases p79_3 (m.d 1 2) (by simp) with h101 | h101
                        · rcases p79_3 (m.d 1 3) (by simp) with h102 | h102
                          · linarith only [h102, h9, hlam]
                          · linarith only [h102, h12, hlam]
                        · linarith only [h10, h101, hlam]
                      · linarith only [h100, h2, hlam]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p79_1, u5ehi1]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h1, hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h9, hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h0, h13, h4, h7, h77, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h13, hlam, p79_1]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h2, hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h10, hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h12, hlam, p79_1]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h70, hlam, p79_1]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h3, hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h11, hlam, p79_0]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [h3, h72, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      rcases p79_3 (m.d 0 1) (by simp) with h121 | h121
                      · rcases p79_3 (m.d 1 2) (by simp) with h122 | h122
                        · rcases p79_3 (m.d 1 3) (by simp) with h123 | h123
                          · linarith only [h123, h13, hlam]
                          · linarith only [h12, h123, hlam]
                        · linarith only [h10, h122, hlam]
                      · linarith only [h121, h2, hlam]
                    · have p79_0 := h79c.1
                      have p79_1 := h79c.2.1
                      have p79_2 := h79c.2.2.1
                      have p79_3 := h79c.2.2.2
                      linarith only [hlam, p79_0]
            · linarith only [h12, h13, h72, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h130 | h130
        · linarith only [h0, h12, h130, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
          · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
            · linarith only [h0, h12, h133, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h135 | h135
              · linarith only [h0, h130, h135, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                · linarith only [h0, h10, h137, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h139 | h139
                  · rcases h1bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h10, h132, h133, h137, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      rcases p140_3 (m.d 0 1) (by simp) with h143 | h143
                      · rcases p140_3 (m.d 1 2) (by simp) with h144 | h144
                        · linarith only [h0, h144, hlam]
                        · linarith only [h144, h9, hlam]
                      · linarith only [h143, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h132, h133, h137, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      rcases p140_3 (m.d 0 1) (by simp) with h149 | h149
                      · rcases p140_3 (m.d 1 2) (by simp) with h150 | h150
                        · linarith only [h0, h150, hlam]
                        · linarith only [h11, h150, hlam]
                      · linarith only [h149, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h0, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      rcases p140_3 (m.d 0 1) (by simp) with h156 | h156
                      · rcases p140_3 (m.d 1 2) (by simp) with h157 | h157
                        · rcases p140_3 (m.d 1 3) (by simp) with h158 | h158
                          · linarith only [h158, h9, hlam]
                          · rcases p140_3 (m.d 1 4) (by simp) with h160 | h160
                            · linarith only [h10, h160, hlam]
                            · linarith only [h12, h160, hlam]
                        · linarith only [h157, h9, hlam]
                      · linarith only [h1, h156, hlam]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h0, h132, h133, h137, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h0, h132, h133, h137, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h1, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h9, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h12, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h130, hlam, p140_1]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h2, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h10, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      rcases p140_3 (m.d 0 1) (by simp) with h174 | h174
                      · rcases p140_3 (m.d 1 2) (by simp) with h175 | h175
                        · rcases p140_3 (m.d 1 3) (by simp) with h176 | h176
                          · linarith only [h12, h176, hlam]
                          · rcases p140_3 (m.d 1 4) (by simp) with h178 | h178
                            · rcases p140_3 (m.d 1 5) (by simp) with h179 | h179
                              · linarith only [h132, h179, hlam]
                              · linarith only [h130, h179, hlam]
                            · linarith only [h12, h178, hlam]
                        · linarith only [h175, h9, hlam]
                      · linarith only [h1, h174, hlam]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h0, h12, h132, h133, h137, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h3, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h11, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      rcases p140_3 (m.d 0 1) (by simp) with h189 | h189
                      · rcases p140_3 (m.d 1 2) (by simp) with h190 | h190
                        · rcases p140_3 (m.d 1 3) (by simp) with h191 | h191
                          · linarith only [h130, h191, hlam]
                          · rcases p140_3 (m.d 1 4) (by simp) with h193 | h193
                            · rcases p140_3 (m.d 1 5) (by simp) with h194 | h194
                              · rcases h2bigk with h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht5b, p195_1, u5ehi2]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h130, h139, h4, h7, h9, hlam, p140_1, p195_2]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h12, h132, h137, h4, h7, hlam, p195_2]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  rcases p195_3 (m.d 0 2) (by simp) with h200 | h200
                                  · rcases p195_3 (m.d 1 2) (by simp) with h201 | h201
                                    · linarith only [h0, h201, hlam]
                                    · linarith only [h11, h201, hlam]
                                  · linarith only [h200, hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h0, hlam, p195_1]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  rcases p195_3 (m.d 0 2) (by simp) with h207 | h207
                                  · rcases p195_3 (m.d 1 2) (by simp) with h208 | h208
                                    · rcases p195_3 (m.d 2 3) (by simp) with h209 | h209
                                      · linarith only [h209, hlam, p195_0]
                                      · rcases p195_3 (m.d 2 4) (by simp) with h211 | h211
                                        · linarith only [h10, h211, hlam]
                                        · linarith only [h133, h211, hlam]
                                    · linarith only [h208, hlam, p195_0]
                                  · linarith only [h207, h4, hlam]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  rcases p195_3 (m.d 0 2) (by simp) with h216 | h216
                                  · rcases p195_3 (m.d 1 2) (by simp) with h217 | h217
                                    · rcases p195_3 (m.d 2 3) (by simp) with h218 | h218
                                      · linarith only [h218, h9, hlam]
                                      · rcases p195_3 (m.d 2 4) (by simp) with h220 | h220
                                        · linarith only [h220, hlam, p195_0]
                                        · rcases p195_3 (m.d 2 5) (by simp) with h222 | h222
                                          · linarith only [h11, h222, hlam]
                                          · linarith only [h137, h222, hlam]
                                    · linarith only [h217, hlam, p195_0]
                                  · linarith only [h216, h5, hlam]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p195_1, u5ehi2]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h4, hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h9, hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h133, hlam, p195_1]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h135, hlam, p195_1]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h5, hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h10, hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h0, h12, h132, h137, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p195_1]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h137, hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h6, hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h11, hlam, p195_0]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p195_1]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [h0, h12, h132, h137, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p195_1]
                                · have p195_0 := h195c.1
                                  have p195_1 := h195c.2.1
                                  have p195_2 := h195c.2.2.1
                                  have p195_3 := h195c.2.2.2
                                  linarith only [hlam, p195_0]
                              · linarith only [h130, h194, hlam]
                            · linarith only [h12, h193, hlam]
                        · linarith only [h190, h9, hlam]
                      · linarith only [h1, h189, hlam]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [h132, hlam, p140_0]
                    · have p140_0 := h140c.1
                      have p140_1 := h140c.2.1
                      have p140_2 := h140c.2.2.1
                      have p140_3 := h140c.2.2.2
                      linarith only [hlam, p140_0]
                  · linarith only [h12, h132, h139, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h250 | h250
            · linarith only [h12, h250, h9, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h252 | h252
              · linarith only [h0, h130, h252, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h254 | h254
                · linarith only [h0, h10, h254, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h256 | h256
                  · rcases h1bigk with h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h11, hc01, hlam, hphi, ht0b, ht5b, p257_1, u5ehi2]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, h12, h132, h256, h4, h7, hlam, p257_2]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, h132, h256, h4, h7, hlam, p257_2]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      rcases p257_3 (m.d 0 1) (by simp) with h262 | h262
                      · rcases p257_3 (m.d 1 2) (by simp) with h263 | h263
                        · linarith only [h0, h263, hlam]
                        · linarith only [h11, h263, hlam]
                      · linarith only [h262, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      rcases p257_3 (m.d 0 1) (by simp) with h269 | h269
                      · rcases p257_3 (m.d 1 2) (by simp) with h270 | h270
                        · rcases p257_3 (m.d 1 3) (by simp) with h271 | h271
                          · linarith only [h271, h9, hlam]
                          · rcases p257_3 (m.d 1 4) (by simp) with h273 | h273
                            · linarith only [h10, h273, hlam]
                            · linarith only [h12, h273, hlam]
                        · linarith only [h270, h9, hlam]
                      · linarith only [h1, h269, hlam]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      rcases p257_3 (m.d 0 1) (by simp) with h278 | h278
                      · rcases p257_3 (m.d 1 2) (by simp) with h279 | h279
                        · rcases p257_3 (m.d 1 3) (by simp) with h280 | h280
                          · linarith only [h280, h9, hlam]
                          · rcases p257_3 (m.d 1 4) (by simp) with h282 | h282
                            · linarith only [h10, h282, hlam]
                            · rcases p257_3 (m.d 1 5) (by simp) with h284 | h284
                              · linarith only [h11, h284, hlam]
                              · linarith only [h132, h284, hlam]
                        · linarith only [h10, h279, hlam]
                      · linarith only [h2, h278, hlam]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht5b, p257_1, u5ehi2]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h1, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h9, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h12, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h130, hlam, p257_1]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h2, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h10, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, h132, h256, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h132, hlam, p257_1]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h3, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h11, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, h132, h256, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, h132, h256, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p257_1]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [hlam, p257_0]
                  · rcases h1bigk with h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h11, hc01, hlam, hphi, ht0b, ht5b, p305_1, u5ehi2]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h0, h12, h256, h4, h7, h8, hlam, p305_2]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      rcases p305_3 (m.d 0 1) (by simp) with h309 | h309
                      · rcases p305_3 (m.d 1 2) (by simp) with h310 | h310
                        · linarith only [h0, h310, hlam]
                        · linarith only [h10, h310, hlam]
                      · linarith only [h309, hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      rcases p305_3 (m.d 0 1) (by simp) with h314 | h314
                      · rcases p305_3 (m.d 1 2) (by simp) with h315 | h315
                        · linarith only [h0, h315, hlam]
                        · linarith only [h11, h315, hlam]
                      · linarith only [h314, hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h0, hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      rcases p305_3 (m.d 0 1) (by simp) with h321 | h321
                      · rcases p305_3 (m.d 1 2) (by simp) with h322 | h322
                        · rcases p305_3 (m.d 1 3) (by simp) with h323 | h323
                          · linarith only [h323, h9, hlam]
                          · rcases p305_3 (m.d 1 4) (by simp) with h325 | h325
                            · linarith only [h10, h325, hlam]
                            · linarith only [h12, h325, hlam]
                        · linarith only [h322, h9, hlam]
                      · linarith only [h1, h321, hlam]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      rcases p305_3 (m.d 0 1) (by simp) with h330 | h330
                      · rcases p305_3 (m.d 1 2) (by simp) with h331 | h331
                        · rcases p305_3 (m.d 1 3) (by simp) with h332 | h332
                          · linarith only [h332, h9, hlam]
                          · rcases p305_3 (m.d 1 4) (by simp) with h334 | h334
                            · linarith only [h10, h334, hlam]
                            · rcases p305_3 (m.d 1 5) (by simp) with h336 | h336
                              · linarith only [h11, h336, hlam]
                              · linarith only [h132, h336, hlam]
                        · linarith only [h10, h331, hlam]
                      · linarith only [h2, h330, hlam]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p305_1, u5ehi1]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h1, hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h9, hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h12, hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h130, hlam, p305_1]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h2, hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h10, hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h0, h12, h256, h4, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p305_1]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h132, hlam, p305_1]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h3, hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [h11, hlam, p305_0]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      rcases p305_3 (m.d 0 1) (by simp) with h354 | h354
                      · rcases p305_3 (m.d 1 2) (by simp) with h355 | h355
                        · rcases p305_3 (m.d 1 3) (by simp) with h356 | h356
                          · linarith only [h130, h356, hlam]
                          · rcases p305_3 (m.d 1 4) (by simp) with h358 | h358
                            · linarith only [h132, h358, hlam]
                            · linarith only [h12, h358, hlam]
                        · linarith only [h355, h9, hlam]
                      · linarith only [h1, h354, hlam]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      rcases p305_3 (m.d 0 1) (by simp) with h363 | h363
                      · rcases p305_3 (m.d 1 2) (by simp) with h364 | h364
                        · rcases p305_3 (m.d 1 3) (by simp) with h365 | h365
                          · linarith only [h130, h365, hlam]
                          · rcases p305_3 (m.d 1 4) (by simp) with h367 | h367
                            · linarith only [h132, h367, hlam]
                            · rcases p305_3 (m.d 1 5) (by simp) with h369 | h369
                              · rcases h2bigk with h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht5b, p370_1, u5ehi2]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h10, h130, h250, h256, h4, h7, h8, hlam, p305_1, p370_2]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h10, h130, h256, h4, h7, h8, hlam, p305_1, p370_2]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  rcases p370_3 (m.d 0 2) (by simp) with h375 | h375
                                  · rcases p370_3 (m.d 1 2) (by simp) with h376 | h376
                                    · linarith only [h0, h376, hlam]
                                    · linarith only [h11, h376, hlam]
                                  · linarith only [h375, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h0, hlam, p370_1]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  rcases p370_3 (m.d 0 2) (by simp) with h382 | h382
                                  · rcases p370_3 (m.d 1 2) (by simp) with h383 | h383
                                    · rcases p370_3 (m.d 2 3) (by simp) with h384 | h384
                                      · linarith only [h384, hlam, p370_0]
                                      · rcases p370_3 (m.d 2 4) (by simp) with h386 | h386
                                        · linarith only [h10, h386, hlam]
                                        · linarith only [h250, h386, hlam]
                                    · linarith only [h383, hlam, p370_0]
                                  · linarith only [h382, h4, hlam]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  rcases p370_3 (m.d 0 2) (by simp) with h391 | h391
                                  · rcases p370_3 (m.d 1 2) (by simp) with h392 | h392
                                    · rcases p370_3 (m.d 2 3) (by simp) with h393 | h393
                                      · linarith only [h393, h9, hlam]
                                      · rcases p370_3 (m.d 2 4) (by simp) with h395 | h395
                                        · linarith only [h395, hlam, p370_0]
                                        · rcases p370_3 (m.d 2 5) (by simp) with h397 | h397
                                          · linarith only [h11, h397, hlam]
                                          · linarith only [h254, h397, hlam]
                                    · linarith only [h392, hlam, p370_0]
                                  · linarith only [h391, h5, hlam]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p370_1, u5ehi2]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h4, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h9, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h250, hlam, p370_1]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h252, hlam, p370_1]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h5, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h10, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h0, h10, h130, h256, h4, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p305_1, p370_1]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h254, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h6, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h11, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p370_1]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h0, h11, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p370_1]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [hlam, p370_0]
                              · linarith only [h132, h369, hlam]
                        · linarith only [h10, h364, hlam]
                      · linarith only [h2, h363, hlam]
                    · have p305_0 := h305c.1
                      have p305_1 := h305c.2.1
                      have p305_2 := h305c.2.2.1
                      have p305_3 := h305c.2.2.2
                      linarith only [hlam, p305_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h422 | h422
      · rcases m.htr 1 3 5 (by decide) (by decide) with h423 | h423
        · linarith only [h0, h11, h423, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h425 | h425
          · linarith only [h0, h10, h11, h425, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h427 | h427
            · linarith only [h0, h11, h427, h6, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h11, h422, h427, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h430 | h430
        · linarith only [h0, h10, h11, h422, h430, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h432 | h432
          · linarith only [h0, h10, h11, h432, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h434 | h434
            · linarith only [h0, h11, h422, h434, h6, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h436 | h436
              · linarith only [h0, h11, h430, h436, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h438 | h438
                · linarith only [h0, h10, h11, h432, h438, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h440 | h440
                  · linarith only [h10, h11, h434, h438, h440, hc23, hc34, hlam, hphi]
                  · rcases h1bigk with h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      rcases p442_3 (m.d 0 1) (by simp) with h444 | h444
                      · rcases p442_3 (m.d 1 2) (by simp) with h445 | h445
                        · linarith only [h445, hlam, p442_0]
                        · rcases p442_3 (m.d 1 3) (by simp) with h447 | h447
                          · linarith only [h1, h447, hlam]
                          · rcases p442_3 (m.d 1 4) (by simp) with h449 | h449
                            · linarith only [h2, h449, hlam]
                            · rcases p442_3 (m.d 1 5) (by simp) with h451 | h451
                              · linarith only [h3, h451, hlam]
                              · linarith only [h11, h451, hlam]
                      · linarith only [h444, hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h0, h4, h422, h440, h7, h8, hlam, p442_2]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      rcases p442_3 (m.d 0 1) (by simp) with h456 | h456
                      · rcases p442_3 (m.d 1 2) (by simp) with h457 | h457
                        · linarith only [h0, h457, hlam]
                        · linarith only [h10, h457, hlam]
                      · linarith only [h456, hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      rcases p442_3 (m.d 0 1) (by simp) with h461 | h461
                      · rcases p442_3 (m.d 1 2) (by simp) with h462 | h462
                        · linarith only [h0, h462, hlam]
                        · rcases p442_3 (m.d 1 3) (by simp) with h464 | h464
                          · linarith only [h1, h464, hlam]
                          · rcases p442_3 (m.d 1 4) (by simp) with h466 | h466
                            · linarith only [h2, h466, hlam]
                            · rcases p442_3 (m.d 1 5) (by simp) with h468 | h468
                              · linarith only [h468, hlam, p442_0]
                              · rcases h2bigk with h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  rcases p470_3 (m.d 0 2) (by simp) with h472 | h472
                                  · rcases p470_3 (m.d 1 2) (by simp) with h473 | h473
                                    · linarith only [h0, h473, hlam]
                                    · rcases p470_3 (m.d 2 3) (by simp) with h475 | h475
                                      · linarith only [h4, h475, hlam]
                                      · rcases p470_3 (m.d 2 4) (by simp) with h477 | h477
                                        · linarith only [h477, h5, hlam]
                                        · rcases p470_3 (m.d 2 5) (by simp) with h479 | h479
                                          · linarith only [h479, h6, hlam]
                                          · linarith only [h11, h479, hlam]
                                  · linarith only [h0, h472, hlam]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h10, h11, h4, h434, h436, h440, h7, h8, hlam, p470_2]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h10, h11, h4, h436, h440, h7, h8, hlam, p470_2]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h0, h10, h11, h434, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h0, hlam, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p442_1, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h11, h434, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p442_1, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h11, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h4, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h9, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h434, hlam, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h436, hlam, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h5, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h10, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h10, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p442_1, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h438, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h6, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h0, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  rcases p470_3 (m.d 0 2) (by simp) with h503 | h503
                                  · rcases p470_3 (m.d 1 2) (by simp) with h504 | h504
                                    · linarith only [h11, h504, hlam]
                                    · linarith only [h504, h9, hlam]
                                  · linarith only [h4, h503, hlam]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  rcases p470_3 (m.d 0 2) (by simp) with h508 | h508
                                  · rcases p470_3 (m.d 1 2) (by simp) with h509 | h509
                                    · linarith only [h11, h509, hlam]
                                    · linarith only [h10, h509, hlam]
                                  · linarith only [h5, h508, hlam]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [hlam, p470_0]
                      · linarith only [h461, hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h0, hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h0, h11, h4, h436, h440, h7, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p442_1]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h0, h11, h4, h422, h436, h440, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p442_1]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h11, hlam, p442_1]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h1, hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h9, hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h422, hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h430, hlam, p442_1]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h2, hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h10, hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h0, h10, h11, h4, h436, h440, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p442_1]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h432, hlam, p442_1]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h3, hlam, p442_0]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [h10, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p442_1]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      rcases p442_3 (m.d 0 1) (by simp) with h532 | h532
                      · rcases p442_3 (m.d 1 2) (by simp) with h533 | h533
                        · linarith only [h11, h533, hlam]
                        · linarith only [h533, h9, hlam]
                      · linarith only [h1, h532, hlam]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      rcases p442_3 (m.d 0 1) (by simp) with h537 | h537
                      · rcases p442_3 (m.d 1 2) (by simp) with h538 | h538
                        · linarith only [h11, h538, hlam]
                        · linarith only [h10, h538, hlam]
                      · linarith only [h2, h537, hlam]
                    · have p442_0 := h442c.1
                      have p442_1 := h442c.2.1
                      have p442_2 := h442c.2.2.1
                      have p442_3 := h442c.2.2.2
                      linarith only [hlam, p442_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h543 | h543
    · linarith only [h0, h10, h5, h543, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h545 | h545
      · linarith only [h10, h545, h9, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h547 | h547
        · linarith only [h0, h10, h5, h547, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h549 | h549
          · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
            · linarith only [h0, h10, h5, h545, h550, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h552 | h552
              · linarith only [h0, h10, h4, h547, h550, h552, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h554 | h554
                · rcases m.htr 3 4 5 (by decide) (by decide) with h555 | h555
                  · rcases h1bigk with h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      rcases p556_3 (m.d 0 1) (by simp) with h558 | h558
                      · rcases p556_3 (m.d 1 2) (by simp) with h559 | h559
                        · linarith only [h559, hlam, p556_0]
                        · rcases p556_3 (m.d 1 3) (by simp) with h561 | h561
                          · linarith only [h1, h561, hlam]
                          · rcases p556_3 (m.d 1 4) (by simp) with h563 | h563
                            · linarith only [h2, h563, hlam]
                            · linarith only [h10, h563, hlam]
                      · linarith only [h558, hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      rcases p556_3 (m.d 0 1) (by simp) with h567 | h567
                      · rcases p556_3 (m.d 1 2) (by simp) with h568 | h568
                        · linarith only [h0, h568, hlam]
                        · linarith only [h568, h9, hlam]
                      · linarith only [h567, hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h549, hc01, hlam, hphi, ht0b, ht5b, p556_1, u5ehi4]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      rcases p556_3 (m.d 0 1) (by simp) with h573 | h573
                      · rcases p556_3 (m.d 1 2) (by simp) with h574 | h574
                        · linarith only [h0, h574, hlam]
                        · rcases p556_3 (m.d 1 3) (by simp) with h576 | h576
                          · linarith only [h1, h576, hlam]
                          · rcases p556_3 (m.d 1 4) (by simp) with h578 | h578
                            · linarith only [h2, h578, hlam]
                            · linarith only [h549, h578, hlam]
                      · linarith only [h573, hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h0, hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h0, h4, h543, h550, h554, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h10, hlam, p556_1]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h543, hlam, p556_1]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h1, hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h9, hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h545, hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h547, hlam, p556_1]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h2, hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      rcases p556_3 (m.d 0 1) (by simp) with h594 | h594
                      · rcases p556_3 (m.d 1 2) (by simp) with h595 | h595
                        · linarith only [h10, h595, hlam]
                        · linarith only [h595, h9, hlam]
                      · linarith only [h1, h594, hlam]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h0, h10, h4, h543, h550, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h3, hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      rcases p556_3 (m.d 0 1) (by simp) with h603 | h603
                      · rcases p556_3 (m.d 1 2) (by simp) with h604 | h604
                        · linarith only [h543, h604, hlam]
                        · linarith only [h604, h9, hlam]
                      · linarith only [h1, h603, hlam]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [h549, hlam, p556_0]
                    · have p556_0 := h556c.1
                      have p556_1 := h556c.2.1
                      have p556_2 := h556c.2.2.1
                      have p556_3 := h556c.2.2.2
                      linarith only [hlam, p556_0]
                  · linarith only [h0, h10, h4, h550, h555, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h10, h549, h554, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h612 | h612
            · linarith only [h0, h10, h5, h612, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h614 | h614
              · linarith only [h10, h614, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h616 | h616
                · linarith only [h0, h10, h4, h549, h612, h616, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h10, h616, h9, hc23, hc45, hlam, hphi, ht34]

set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h619 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 5 (by decide) (by decide) with h620 | h620
  · linarith only [h0, h4, h620, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h622 | h622
    · rcases m.htr 1 3 5 (by decide) (by decide) with h623 | h623
      · rcases m.htr 1 4 5 (by decide) (by decide) with h624 | h624
        · linarith only [h0, h4, h619, h624, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h626 | h626
          · rcases m.htr 2 3 5 (by decide) (by decide) with h627 | h627
            · rcases m.htr 2 4 5 (by decide) (by decide) with h628 | h628
              · linarith only [h0, h4, h619, h620, h624, h627, h628, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h630 | h630
                · linarith only [h619, h620, h626, h628, h630, hlam]
                · rcases h1bigk with h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    rcases p632_3 (m.d 0 1) (by simp) with h634 | h634
                    · rcases p632_3 (m.d 1 2) (by simp) with h635 | h635
                      · linarith only [h635, hlam, p632_0]
                      · rcases p632_3 (m.d 1 3) (by simp) with h637 | h637
                        · linarith only [h1, h637, hlam]
                        · linarith only [h637, h9, hlam]
                    · linarith only [h634, hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h623, hc01, hlam, hphi, ht0b, ht5b, p632_1, u5ehi3]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    rcases p632_3 (m.d 0 1) (by simp) with h642 | h642
                    · rcases p632_3 (m.d 1 2) (by simp) with h643 | h643
                      · linarith only [h0, h643, hlam]
                      · linarith only [h619, h643, hlam]
                    · linarith only [h642, hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    rcases p632_3 (m.d 0 1) (by simp) with h647 | h647
                    · rcases p632_3 (m.d 1 2) (by simp) with h648 | h648
                      · linarith only [h0, h648, hlam]
                      · rcases p632_3 (m.d 1 3) (by simp) with h650 | h650
                        · linarith only [h1, h650, hlam]
                        · linarith only [h623, h650, hlam]
                    · linarith only [h647, hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h0, hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h9, hlam, p632_1]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h0, h4, h620, h628, h7, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p632_1]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h620, hlam, p632_1]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h1, hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h1, h619, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p632_1]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    rcases p632_3 (m.d 0 1) (by simp) with h662 | h662
                    · rcases p632_3 (m.d 1 2) (by simp) with h663 | h663
                      · linarith only [h663, h9, hlam]
                      · linarith only [h619, h663, hlam]
                    · linarith only [h2, h662, hlam]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h0, h4, h619, h620, h626, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p632_1]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h2, hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h619, hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h622, hlam, p632_1]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h624, hlam, p632_1]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h3, hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h3, h619, h626, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p632_1]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [h623, hlam, p632_0]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    rcases p632_3 (m.d 0 1) (by simp) with h676 | h676
                    · rcases p632_3 (m.d 1 2) (by simp) with h677 | h677
                      · linarith only [h620, h677, hlam]
                      · linarith only [h619, h677, hlam]
                    · linarith only [h2, h676, hlam]
                  · have p632_0 := h632c.1
                    have p632_1 := h632c.2.1
                    have p632_2 := h632c.2.2.1
                    have p632_3 := h632c.2.2.2
                    linarith only [hlam, p632_0]
            · linarith only [h623, h627, h9, hlam]
          · linarith only [h0, h4, h623, h626, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h684 | h684
        · linarith only [h0, h4, h619, h684, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h686 | h686
          · rcases m.htr 2 3 5 (by decide) (by decide) with h687 | h687
            · linarith only [h0, h4, h619, h623, h687, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h689 | h689
              · linarith only [h619, h684, h687, h689, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h691 | h691
                · linarith only [h619, h686, h687, h689, h691, h9, hlam]
                · linarith only [h0, h4, h619, h686, h687, h691, h7, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h4, h619, h686, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h619, h622, h9, hlam]

set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h619 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h696 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  linarith only [h0, h4, h696, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]

end R2N4
